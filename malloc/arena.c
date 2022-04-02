/* Malloc implementation for multiple threads without lock contention.
	 Copyright (C) 2001-2018 Free Software Foundation, Inc.
	 This file is part of the GNU C Library.
	 Contributed by Wolfram Gloger <wg@malloc.de>, 2001.

	 The GNU C Library is free software; you can redistribute it and/or
	 modify it under the terms of the GNU Lesser General Public License as
	 published by the Free Software Foundation; either version 2.1 of the
	 License, or (at your option) any later version.

	 The GNU C Library is distributed in the hope that it will be useful,
	 but WITHOUT ANY WARRANTY; without even the implied warranty of
	 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.	See the GNU
	 Lesser General Public License for more details.

	 You should have received a copy of the GNU Lesser General Public
	 License along with the GNU C Library; see the file COPYING.LIB.	If
	 not, see <http://www.gnu.org/licenses/>.	*/

#include <stdbool.h>

#if HAVE_TUNABLES
# define TUNABLE_NAMESPACE malloc
#endif
#include <elf/dl-tunables.h>

/* Compile-time constants.	*/

#define HEAP_MIN_SIZE (32 * 1024)
#ifndef HEAP_MAX_SIZE
# ifdef DEFAULT_MMAP_THRESHOLD_MAX
#	define HEAP_MAX_SIZE (2 * DEFAULT_MMAP_THRESHOLD_MAX)
# else
#	define HEAP_MAX_SIZE (1024 * 1024) /* must be a power of two */
# endif
#endif

/* HEAP_MIN_SIZE and HEAP_MAX_SIZE limit the size of mmap()ed heaps
	 that are dynamically created for multi-threaded programs.	The
	 maximum size must be a power of two, for fast determination of
	 which heap belongs to a chunk.	It should be much larger than the
	 mmap threshold, so that requests with a size just below that
	 threshold can be fulfilled without creating too many heaps.	*/

/***************************************************************************/

#define top(ar_ptr) ((ar_ptr)->top)

/* A heap is a single contiguous memory region holding (coalesceable)
	malloc_chunks.	It is allocated with mmap() and always starts at an
	address aligned to HEAP_MAX_SIZE.	*/

typedef struct _heap_info
{
	mstate ar_ptr; /* Arena for this heap. */
	struct _heap_info *prev; /* Previous heap. */
	size_t size;	 /* Current size in bytes. */
	size_t mprotect_size; /* Size in bytes that has been mprotected
													PROT_READ|PROT_WRITE.	*/
	/* Make sure the following data is properly aligned, particularly
		 that sizeof (heap_info) + 2 * SIZE_SZ is a multiple of
		 MALLOC_ALIGNMENT. */
	char pad[-6 * SIZE_SZ & MALLOC_ALIGN_MASK];
} heap_info;

/* Get a compile-time error if the heap_info padding is not correct
	to make alignment work as expected in sYSMALLOc.	*/
extern int sanity_check_heap_info_alignment[(sizeof (heap_info)
																						 + 2 * SIZE_SZ) % MALLOC_ALIGNMENT
																						? -1 : 1];

/* Thread specific data.	*/
//ptmalloc初始化时，thread_arena被设置为main arena
//创建新的arena时，thread_arena被设置为新的arena
//每个thread的值不同，未使用过ptmalloc的thread的初始值为Null
//*各个thread对应的该值在ptmalloc将某个arena和此thread绑定时记录
//*上一个记录的值在由于指向的arena被占用而替换arena时被覆盖
//*便于各个thread尽量减少arena的更换，尽量选择使用和上一次分配相同的arena
static __thread mstate thread_arena attribute_tls_model_ie;

/* Arena free list.	free_list_lock synchronizes access to the
	free_list variable below, and the next_free and attached_threads
	members of struct malloc_state objects.	No other locks must be
	acquired after free_list_lock has been acquired.	*/

__libc_lock_define_initialized (static, free_list_lock);
static size_t narenas = 1;
static mstate free_list;	//free_list为一个malloc state结构体指针

/* list_lock prevents concurrent writes to the next member of struct
	malloc_state objects.

	Read access to the next member is supposed to synchronize with the
	atomic_write_barrier and the write to the next member in
	_int_new_arena.	This suffers from data races; see the FIXME
	comments in _int_new_arena and reused_arena.

	list_lock also prevents concurrent forks.	At the time list_lock is
	acquired, no arena lock must have been acquired, but it is
	permitted to acquire arena locks subsequently, while list_lock is
	acquired.
*/
__libc_lock_define_initialized (static, list_lock);

/* Already initialized? */
int __malloc_initialized = -1;

/**************************************************************************/


/* 
	arena_get() acquires an arena and locks the corresponding mutex.
	First, try the one last locked successfully by this thread.	(This
	is the common case and handled with a macro for speed.)	Then, loop
	once over the circularly linked list of arenas.	If no arena is
	readily available, create a new one.	In this latter case, `size'
	is just a hint as to how much memory will be required immediately
	in the new arena. 
*/
//检查thread_arena(当前线程上次使用的arena)是否为可用的arena，若是，则加锁返回
//若不是，则进入arena_get2执行
#define arena_get(ptr, size) 							\
	do {												\
		/*未使用过ptmalloc的thread的thread_arena为Null*/  \
		ptr = thread_arena;								\
		arena_lock (ptr, size);							\
	} while (0)

#define arena_lock(ptr, size) 							\
	do {												\
		if (ptr)										\
			/*阻塞操作，若获取不到对应的arena则会等待*/		  \
			__libc_lock_lock (ptr->mutex);				\
		else											\
			ptr = arena_get2 ((size), NULL);			\
	} while (0)

/* find the heap and corresponding arena for a given ptr */

#define heap_for_ptr(ptr) \
	((heap_info *) ((unsigned long) (ptr) & ~(HEAP_MAX_SIZE - 1)))
#define arena_for_chunk(ptr) \
	(chunk_main_arena (ptr) ? &main_arena : heap_for_ptr (ptr)->ar_ptr)


/**************************************************************************/

/* atfork support.	*/

/* The following three functions are called around fork from a
	 multi-threaded process.	We do not use the general fork handler
	 mechanism to make sure that our handlers are the last ones being
	 called, so that other fork handlers can use the malloc
	 subsystem.	*/

void
__malloc_fork_lock_parent (void)
{
	if (__malloc_initialized < 1)
		return;

	/* 
		We do not acquire free_list_lock here because we completely
		reconstruct free_list in __malloc_fork_unlock_child.
	*/

	__libc_lock_lock (list_lock);

	for (mstate ar_ptr = &main_arena;; )
		{
			__libc_lock_lock (ar_ptr->mutex);
			ar_ptr = ar_ptr->next;
			if (ar_ptr == &main_arena)
				break;
		}
}

void
__malloc_fork_unlock_parent (void)
{
	if (__malloc_initialized < 1)
		return;

	for (mstate ar_ptr = &main_arena;; )
		{
			__libc_lock_unlock (ar_ptr->mutex);
			ar_ptr = ar_ptr->next;
			if (ar_ptr == &main_arena)
				break;
		}
	__libc_lock_unlock (list_lock);
}

//创建子进程时调用
void
__malloc_fork_unlock_child (void)
{
	//若此时父进程尚未初始化ptmalloc，则直接退出
	if (__malloc_initialized < 1)
		return;

	//初始化free list锁，初始化free list
	__libc_lock_init (free_list_lock);
	//若调用子进程的线程的thread_arena存在，则设置子进程中对应arena的attached_threads字段
	//(子进程程序内存空间分布完全由父进程的调用fork的线程复制而来)
	if (thread_arena != NULL)
		thread_arena->attached_threads = 1;
	free_list = NULL;
	//将除子进程当前使用的arena以外的所有arena放入free list中
	for (mstate ar_ptr = &main_arena;; )
	{
		//此处子进程还未开始运行，不需要对free list & list & arena加锁
		__libc_lock_init (ar_ptr->mutex);
		//将arenas放在free list的最前方
		if (ar_ptr != thread_arena)
		{
			/* This arena is no longer attached to any thread.	*/
			ar_ptr->attached_threads = 0;
			ar_ptr->next_free = free_list;
			free_list = ar_ptr;
		}
		ar_ptr = ar_ptr->next;
		if (ar_ptr == &main_arena)
			break;
	}
	__libc_lock_init (list_lock);
}

#if HAVE_TUNABLES
static inline int do_set_mallopt_check (int32_t value);
void
TUNABLE_CALLBACK (set_mallopt_check) (tunable_val_t *valp)
{
	int32_t value = (int32_t) valp->numval;
	if (value != 0)
		__malloc_check_init ();
}

# define TUNABLE_CALLBACK_FNDECL(__name, __type) \
static inline int do_ ## __name (__type value);							\
void												\
TUNABLE_CALLBACK (__name) (tunable_val_t *valp)							\
{												\
	__type value = (__type) (valp)->numval;							\
	do_ ## __name (value);									\
}

TUNABLE_CALLBACK_FNDECL (set_mmap_threshold, size_t)
TUNABLE_CALLBACK_FNDECL (set_mmaps_max, int32_t)
TUNABLE_CALLBACK_FNDECL (set_top_pad, size_t)
TUNABLE_CALLBACK_FNDECL (set_perturb_byte, int32_t)
TUNABLE_CALLBACK_FNDECL (set_trim_threshold, size_t)
TUNABLE_CALLBACK_FNDECL (set_arena_max, size_t)
TUNABLE_CALLBACK_FNDECL (set_arena_test, size_t)
#if USE_TCACHE
TUNABLE_CALLBACK_FNDECL (set_tcache_max, size_t)
TUNABLE_CALLBACK_FNDECL (set_tcache_count, size_t)
TUNABLE_CALLBACK_FNDECL (set_tcache_unsorted_limit, size_t)
#endif
#else
/* Initialization routine. */
#include <string.h>
extern char **_environ;

static char *
next_env_entry (char ***position)
{
	char **current = *position;
	char *result = NULL;

	while (*current != NULL)
		{
			if (__builtin_expect ((*current)[0] == 'M', 0)
					&& (*current)[1] == 'A'
					&& (*current)[2] == 'L'
					&& (*current)[3] == 'L'
					&& (*current)[4] == 'O'
					&& (*current)[5] == 'C'
					&& (*current)[6] == '_')
				{
					result = &(*current)[7];

					/* Save current position for next visit.	*/
					*position = ++current;

					break;
				}

			++current;
		}

	return result;
}
#endif


#ifdef SHARED
static void *
__failing_morecore (ptrdiff_t d)
{
	return (void *) MORECORE_FAILURE;
}

extern struct dl_open_hook *_dl_open_hook;
libc_hidden_proto (_dl_open_hook);
#endif

static void
ptmalloc_init (void)
{
	//未初始化为-1
	//若ptmalloc已初始化，则直接返回
	if (__malloc_initialized >= 0)
		return;
	//设置初始化位
	__malloc_initialized = 0;

#ifdef SHARED
	/* 
		In case this libc copy is in a non-default namespace, never use brk.
		Likewise if dlopened from statically linked program.
	*/
	Dl_info di;
	struct link_map *l;

	if (_dl_open_hook != NULL || (_dl_addr (ptmalloc_init, &di, &l, NULL) != 0
			&& l->l_ns != LM_ID_BASE))
		__morecore = __failing_morecore;
#endif
	//调用ptmalloc_init函数的线程为主线程，将其最近使用的arena标识为main arena
	thread_arena = &main_arena;
	//初始化main arena的malloc state结构体实例
	malloc_init_state (&main_arena);

#if HAVE_TUNABLES
	TUNABLE_GET (check, int32_t, TUNABLE_CALLBACK (set_mallopt_check));
	TUNABLE_GET (top_pad, size_t, TUNABLE_CALLBACK (set_top_pad));
	TUNABLE_GET (perturb, int32_t, TUNABLE_CALLBACK (set_perturb_byte));
	TUNABLE_GET (mmap_threshold, size_t, TUNABLE_CALLBACK (set_mmap_threshold));
	TUNABLE_GET (trim_threshold, size_t, TUNABLE_CALLBACK (set_trim_threshold));
	TUNABLE_GET (mmap_max, int32_t, TUNABLE_CALLBACK (set_mmaps_max));
	TUNABLE_GET (arena_max, size_t, TUNABLE_CALLBACK (set_arena_max));
	TUNABLE_GET (arena_test, size_t, TUNABLE_CALLBACK (set_arena_test));
# if USE_TCACHE
	TUNABLE_GET (tcache_max, size_t, TUNABLE_CALLBACK (set_tcache_max));
	TUNABLE_GET (tcache_count, size_t, TUNABLE_CALLBACK (set_tcache_count));
	TUNABLE_GET (tcache_unsorted_limit, size_t,
	TUNABLE_CALLBACK (set_tcache_unsorted_limit));
# endif

#else
	const char *s = NULL;
	if (__glibc_likely (_environ != NULL))
	{
		char **runp = _environ;
		char *envline;

		while (__builtin_expect ((envline = next_env_entry (&runp)) != NULL,0))
		{
			size_t len = strcspn (envline, "=");

			if (envline[len] != '=')
			/* 
				This is a "MALLOC_" variable at the end of the string
				without a '=' character.	Ignore it since otherwise we
				will access invalid memory below.
			*/
				continue;

			switch (len)
			{
			case 6:
				if (memcmp (envline, "CHECK_", 6) == 0)
					s = &envline[7];
				break;
			case 8:
				if (!__builtin_expect (__libc_enable_secure, 0))
					{
						if (memcmp (envline, "TOP_PAD_", 8) == 0)
							__libc_mallopt (M_TOP_PAD, atoi (&envline[9]));
						else if (memcmp (envline, "PERTURB_", 8) == 0)
							__libc_mallopt (M_PERTURB, atoi (&envline[9]));
					}
				break;
			case 9:
				if (!__builtin_expect (__libc_enable_secure, 0))
					{
						if (memcmp (envline, "MMAP_MAX_", 9) == 0)
							__libc_mallopt (M_MMAP_MAX, atoi (&envline[10]));
						else if (memcmp (envline, "ARENA_MAX", 9) == 0)
							__libc_mallopt (M_ARENA_MAX, atoi (&envline[10]));
					}
				break;
			case 10:
				if (!__builtin_expect (__libc_enable_secure, 0))
					{
						if (memcmp (envline, "ARENA_TEST", 10) == 0)
							__libc_mallopt (M_ARENA_TEST, atoi (&envline[11]));
					}
				break;
			case 15:
				if (!__builtin_expect (__libc_enable_secure, 0))
					{
						if (memcmp (envline, "TRIM_THRESHOLD_", 15) == 0)
							__libc_mallopt (M_TRIM_THRESHOLD, atoi (&envline[16]));
						else if (memcmp (envline, "MMAP_THRESHOLD_", 15) == 0)
							__libc_mallopt (M_MMAP_THRESHOLD, atoi (&envline[16]));
					}
				break;
			default:
				break;
			}
		}
	}
	if (s && s[0] != '\0' && s[0] != '0')
		__malloc_check_init ();
#endif
//读取并执行__malloc_initialize_hook
#if HAVE_MALLOC_INIT_HOOK
	void (*hook) (void) = atomic_forced_read (__malloc_initialize_hook);
	if (hook != NULL)
		(*hook)();
#endif
	//设置位，表明ptmalloc初始化完成
	__malloc_initialized = 1;
}

/* Managing heaps and arenas (for concurrent threads) */

#if MALLOC_DEBUG > 1

/* Print the complete contents of a single heap to stderr. */

static void
dump_heap (heap_info *heap)
{
	char *ptr;
	mchunkptr p;

	fprintf (stderr, "Heap %p, size %10lx:\n", heap, (long) heap->size);
	ptr = (heap->ar_ptr != (mstate) (heap + 1)) ?
				(char *) (heap + 1) : (char *) (heap + 1) + sizeof (struct malloc_state);
	p = (mchunkptr) (((unsigned long) ptr + MALLOC_ALIGN_MASK) &
									~MALLOC_ALIGN_MASK);
	for (;; )
		{
			fprintf (stderr, "chunk %p size %10lx", p, (long) p->size);
			if (p == top (heap->ar_ptr))
				{
					fprintf (stderr, " (top)\n");
					break;
				}
			else if (p->size == (0 | PREV_INUSE))
				{
					fprintf (stderr, " (fence)\n");
					break;
				}
			fprintf (stderr, "\n");
			p = next_chunk (p);
		}
}
#endif /* MALLOC_DEBUG > 1 */

/* If consecutive mmap (0, HEAP_MAX_SIZE << 1, ...) calls return decreasing
	addresses as opposed to increasing, new_heap would badly fragment the
	address space.	In that case remember the second HEAP_MAX_SIZE part
	aligned to HEAP_MAX_SIZE from last mmap (0, HEAP_MAX_SIZE << 1, ...)
	call (if it is already aligned) and try to reuse it next time.	We need
	no locking for it, as kernel ensures the atomicity for us - worst case
	we'll call mmap (addr, HEAP_MAX_SIZE, ...) for some value of addr in
	multiple threads, but only one will succeed.	*/
static char *aligned_heap_area;

/* Create a new heap.	size is automatically rounded up to a multiple
	 of the page size. */
//返回新创建的heap头指针(指向heap_info结构体)
static heap_info *
new_heap (size_t size, size_t top_pad)
{
	size_t pagesize = GLRO (dl_pagesize);
	char *p1, *p2;
	unsigned long ul;
	heap_info *h;

	//新heap的size若小于HEAP_MIN_SIZE，则创建HEAP_MIN_SIZE大小的heap
	//否则，创建相应top pad(top chunk) + size向上对齐到page整数倍大小的chunk
	//若请求创建的heap size大于HEAP_MAX_SIZE,则返回0,创建失败
	if (size + top_pad < HEAP_MIN_SIZE)
		size = HEAP_MIN_SIZE;
	else if (size + top_pad <= HEAP_MAX_SIZE)
		size += top_pad;
	else if (size > HEAP_MAX_SIZE)
		return 0;
	else
		size = HEAP_MAX_SIZE;
	size = ALIGN_UP (size, pagesize);

	/* A memory region aligned to a multiple of HEAP_MAX_SIZE is needed.
		No swap space needs to be reserved for the following large
		mapping (on Linux, this is the case for all non-writable mappings
		 anyway). */
	p2 = MAP_FAILED;
	//若设置了aligned_heap_area,则说明此时有一块最佳内存可以使用，由该变量给出
	//此块内存是上次使用mmap分配 HEAP_MAX_SIZE << 1 大小后unmmap的后半部分
	if (aligned_heap_area)
	{
		//从aligned_heap_area指向的区域开始分配最大heap size的空间
		p2 = (char *) MMAP (aligned_heap_area, HEAP_MAX_SIZE, PROT_NONE,
												MAP_NORESERVE);
		aligned_heap_area = NULL;
		//若mmap对heap分配成功但heap指针没有对齐HEAP_MAX_SIZE的整数倍位置，则重新分配
		if (p2 != MAP_FAILED && ((unsigned long) p2 & (HEAP_MAX_SIZE - 1)))
		{
			__munmap (p2, HEAP_MAX_SIZE);
			p2 = MAP_FAILED;
		}
	}
	//若mmap分配失败或heap指针没有对齐HEAP_MAX_SIZE的整数倍位置
	if (p2 == MAP_FAILED)
	{
		//分配两倍HEAP_MAX_SIZE大小的空间，确保其中HEAP_MAX_SIZE大小的空间可以对齐到HEAP_MAX_SIZE的整数倍地址位置
		p1 = (char *) MMAP (0, HEAP_MAX_SIZE << 1, PROT_NONE, MAP_NORESERVE);
		if (p1 != MAP_FAILED)
		{
			//找到对齐到的位置的指针
			p2 = (char *) (((unsigned long) p1 + (HEAP_MAX_SIZE - 1))
								& ~(HEAP_MAX_SIZE - 1));
			//找到前侧多余的空间大小
			ul = p2 - p1;
			//若前侧有多余的空间，则返还给系统
			if (ul)
				__munmap (p1, ul);
			//若没有多余的空间，则将后方一半的空间设置为下次创建heap时使用的空间(确定可以使用这部分空间，降低空间分配不成功可能性)
			else
				
				aligned_heap_area = p2 + HEAP_MAX_SIZE;
			//将后侧多余的空间返还
			__munmap (p2 + HEAP_MAX_SIZE, HEAP_MAX_SIZE - ul);
		}
		//仍然失败，就看概率了
		else
		{
			//随机分配一块空间，查看是否对齐，若对齐则使用；不对齐则返还给系统
			p2 = (char *) MMAP (0, HEAP_MAX_SIZE, PROT_NONE, MAP_NORESERVE);
			if (p2 == MAP_FAILED)
				return 0;

			if ((unsigned long) p2 & (HEAP_MAX_SIZE - 1))
			{
				__munmap (p2, HEAP_MAX_SIZE);
				return 0;
			}
		}
	}
	//暂且忽略不计
	if (__mprotect (p2, size, PROT_READ | PROT_WRITE) != 0)
	{
		__munmap (p2, HEAP_MAX_SIZE);
		return 0;
	}
	h = (heap_info *) p2;
	h->size = size;
	h->mprotect_size = size;
	LIBC_PROBE (memory_heap_new, 2, h, h->size);
	return h;
}

//增加heap大小
static int
grow_heap (heap_info *h, long diff)
{
	size_t pagesize = GLRO (dl_pagesize);
	long new_size;
	//将要增加的大小向上对齐到内存页大小的整数倍
	diff = ALIGN_UP (diff, pagesize);
	//记录新的size
	new_size = (long) h->size + diff;
	//若新的heap size大于了heap最大size，则返回 -1，表示heap增长失败
	if ((unsigned long) new_size > (unsigned long) HEAP_MAX_SIZE)
		return -1;
	//?这段检测比较迷惑，之后再来调整
	if ((unsigned long) new_size > h->mprotect_size)
	{
		if (__mprotect ((char *) h + h->mprotect_size,
										(unsigned long) new_size - h->mprotect_size,
										PROT_READ | PROT_WRITE) != 0)
			return -2;

		h->mprotect_size = new_size;
	}
	//调整heap_info结构体(heap管理结构体)中的size
	h->size = new_size;
	LIBC_PROBE (memory_heap_more, 2, h, h->size);
	//大小增长成功，返回0
	return 0;
}

/* Shrink a heap.	*/

static int
shrink_heap (heap_info *h, long diff)
{
	long new_size;

	new_size = (long) h->size - diff;
	if (new_size < (long) sizeof (*h))
		return -1;

	/* Try to re-map the extra heap space freshly to save memory, and make it
		 inaccessible.	See malloc-sysdep.h to know when this is true.	*/
	if (__glibc_unlikely (check_may_shrink_heap ()))
		{
			if ((char *) MMAP ((char *) h + new_size, diff, PROT_NONE,
												 MAP_FIXED) == (char *) MAP_FAILED)
				return -2;

			h->mprotect_size = new_size;
		}
	else
		__madvise ((char *) h + new_size, diff, MADV_DONTNEED);
	/*fprintf(stderr, "shrink %p %08lx\n", h, new_size);*/

	h->size = new_size;
	LIBC_PROBE (memory_heap_less, 2, h, h->size);
	return 0;
}

/* Delete a heap. */

#define delete_heap(heap) \
	do {												\
			if ((char *) (heap) + HEAP_MAX_SIZE == aligned_heap_area)					\
				aligned_heap_area = NULL;								\
			__munmap ((char *) (heap), HEAP_MAX_SIZE);						\
		} while (0)

static int
heap_trim (heap_info *heap, size_t pad)
{
	mstate ar_ptr = heap->ar_ptr;
	unsigned long pagesz = GLRO (dl_pagesize);
	mchunkptr top_chunk = top (ar_ptr), p, bck, fwd;
	heap_info *prev_heap;
	long new_size, top_size, top_area, extra, prev_size, misalign;

	/* Can this heap go away completely? */
	while (top_chunk == chunk_at_offset (heap, sizeof (*heap)))
		{
			prev_heap = heap->prev;
			prev_size = prev_heap->size - (MINSIZE - 2 * SIZE_SZ);
			p = chunk_at_offset (prev_heap, prev_size);
			/* fencepost must be properly aligned.	*/
			misalign = ((long) p) & MALLOC_ALIGN_MASK;
			p = chunk_at_offset (prev_heap, prev_size - misalign);
			assert (chunksize_nomask (p) == (0 | PREV_INUSE)); /* must be fencepost */
			p = prev_chunk (p);
			new_size = chunksize (p) + (MINSIZE - 2 * SIZE_SZ) + misalign;
			assert (new_size > 0 && new_size < (long) (2 * MINSIZE));
			if (!prev_inuse (p))
				new_size += prev_size (p);
			assert (new_size > 0 && new_size < HEAP_MAX_SIZE);
			if (new_size + (HEAP_MAX_SIZE - prev_heap->size) < pad + MINSIZE + pagesz)
				break;
			ar_ptr->system_mem -= heap->size;
			LIBC_PROBE (memory_heap_free, 2, heap, heap->size);
			delete_heap (heap);
			heap = prev_heap;
			if (!prev_inuse (p)) /* consolidate backward */
				{
					p = prev_chunk (p);
					unlink (ar_ptr, p, bck, fwd);
				}
			assert (((unsigned long) ((char *) p + new_size) & (pagesz - 1)) == 0);
			assert (((char *) p + new_size) == ((char *) heap + heap->size));
			top (ar_ptr) = top_chunk = p;
			set_head (top_chunk, new_size | PREV_INUSE);
			/*check_chunk(ar_ptr, top_chunk);*/
		}

	/* 
		Uses similar logic for per-thread arenas as the main arena with systrim
		and _int_free by preserving the top pad and rounding down to the nearest
		page.
	*/
	top_size = chunksize (top_chunk);
	if ((unsigned long)(top_size) <
			(unsigned long)(mp_.trim_threshold))
		return 0;

	top_area = top_size - MINSIZE - 1;
	if (top_area < 0 || (size_t) top_area <= pad)
		return 0;

	/* Release in pagesize units and round down to the nearest page.	*/
	extra = ALIGN_DOWN(top_area - pad, pagesz);
	if (extra == 0)
		return 0;

	/* Try to shrink. */
	if (shrink_heap (heap, extra) != 0)
		return 0;

	ar_ptr->system_mem -= extra;

	/* Success. Adjust top accordingly. */
	set_head (top_chunk, (top_size - extra) | PREV_INUSE);
	/*check_chunk(ar_ptr, top_chunk);*/
	return 1;
}

/* Create a new arena with initial size "size".	*/

/* If REPLACED_ARENA is not NULL, detach it from this thread.	Must be
	called while free_list_lock is held.
*/
static void
detach_arena (mstate replaced_arena)
{
	if (replaced_arena != NULL)
		{
			assert (replaced_arena->attached_threads > 0);
			/* 
				The current implementation only detaches from main_arena in
				case of allocation failure.	This means that it is likely not
				beneficial to put the arena on free_list even if the
				reference count reaches zero.
			*/
			--replaced_arena->attached_threads;
		}
}

//建立新的arena，必为thread arena
static mstate
_int_new_arena (size_t size)
{
	mstate a;
	heap_info *h;
	char *ptr;
	unsigned long misalign;

	h = new_heap (size + (sizeof (*h) + sizeof (*a) + MALLOC_ALIGNMENT),
								mp_.top_pad);
	//请求不成功
	if (!h)
	{
		/* Maybe size is too large to fit in a single heap.	So, just try
			to create a minimally-sized arena and let _int_malloc() attempt
			to deal with the large request via mmap_chunk().
		*/
		//创建最小的arena大小，之后使用_int_malloc进行需要的内存请求
		h = new_heap (sizeof (*h) + sizeof (*a) + MALLOC_ALIGNMENT, mp_.top_pad);
		if (!h)
			return 0;
	}
	//mmap空间的顶部为heap_info结构体的实例存储的位置
	//设置指针为指向距离mmap空间顶部一个heap_info结构体长度的地址，将其强制转化为malloc_state结构体指针
	a = h->ar_ptr = (mstate) (h + 1);
	//初始化malloc_state结构体
	malloc_init_state (a);
	a->attached_threads = 1;
	/*a->next = NULL;*/
	//直接将当前arena空间占用量设置为size大小
	a->system_mem = a->max_system_mem = h->size;

	//将top chunk指针设置到malloc_state结构体实例后方一个malloc_state结构体长度的地方
	ptr = (char *) (a + 1);
	//在malloc_state结构体后放置top chunk
	//将指针向后对齐到 2 * SIZE_SZ 大小的位置
	misalign = (unsigned long) chunk2mem (ptr) & MALLOC_ALIGN_MASK;
	if (misalign > 0)
		ptr += MALLOC_ALIGNMENT - misalign;
	top (a) = (mchunkptr) ptr;
	set_head (top (a), (((char *) h + h->size) - ptr) | PREV_INUSE);

	LIBC_PROBE (memory_arena_new, 2, a, size);
	mstate replaced_arena = thread_arena;
	thread_arena = a;
	//对此arena初始化互斥锁
	__libc_lock_init (a->mutex);
	//对arena list加锁，以便加入新的arena
	__libc_lock_lock (list_lock);

	//将新的arena加入到紧跟在main arena后方的位置
	a->next = main_arena.next;
	/* FIXME: The barrier is an attempt to synchronize with read access
		in reused_arena, which does not acquire list_lock while
		traversing the list.
	*/
	atomic_write_barrier ();
	main_arena.next = a;
	//解锁arena list
	__libc_lock_unlock (list_lock);

	__libc_lock_lock (free_list_lock);
	detach_arena (replaced_arena);
	__libc_lock_unlock (free_list_lock);

	/* Lock this arena.	NB: Another thread may have been attached to
		this arena because the arena is now accessible from the
		main_arena.next list and could have been picked by reused_arena.
		This can only happen for the last arena created (before the arena
		limit is reached).	At this point, some arena has to be attached
		to two threads.	We could acquire the arena lock before list_lock
		to make it less likely that reused_arena picks this new arena,
		but this could result in a deadlock with
		__malloc_fork_lock_parent.
	*/
	//为此arena加锁
	__libc_lock_lock (a->mutex);

	return a;
}


/* Remove an arena from free_list.	*/
static mstate
get_free_list (void)
{
	//从arena_get()->arena_get2()调用时，thread_arena == NULL
	//获取本thread上次使用的arena
	mstate replaced_arena = thread_arena;
	//free list用单向链表的形式组织所有当前未在使用的arena
	//获取free_list表头
	mstate result = free_list;
	//若表头指针不为Null(free list中存在arena)，则直接使用
	if (result != NULL)
	{
		//对free list加锁
		__libc_lock_lock (free_list_lock);
		//再次获取free_list指针，防止检测if语句检测完后到加锁前存在问题
		//result为获取到的一个在free_list中的arena
		result = free_list;
		if (result != NULL)
		{
			//更新free_list指针为下一个位于free list中的arena的指针
			//将result从free list中删除(free list为单向链表，result为其第一项，操作合理)
			free_list = result->next_free;
			/* The arena will be attached to this thread.	*/
			//!所有在free list中的arena的attached_threads域必为0
			assert (result->attached_threads == 0);
			//将获取到的result的attached_threads域设置为1
			result->attached_threads = 1;
			//从arena_get()->arena_get2()调用时，不产生作用(replaced_arena == NULL)
			//调整对应arena的attached_threads字段
			detach_arena (replaced_arena);
		}
		__libc_lock_unlock (free_list_lock);

		if (result != NULL)
		{
			LIBC_PROBE (memory_arena_reuse_free_list, 1, result);
			__libc_lock_lock (result->mutex);
			//若成功，则将此thread的thread_arena(上次分配使用的arena)变量设置为result
			thread_arena = result;
		}
	}

	return result;
}

/* Remove the arena from the free list (if it is present).
	 free_list_lock must have been acquired by the caller.	*/
static void
remove_from_free_list (mstate arena)
{
	//指针首先指向free_list变量的地址
	mstate *previous = &free_list;
	//若指定的arena位于free_list中，则
	for (mstate p = free_list; p != NULL; p = p->next_free)
	{
		//free list中arena的attached_threads域必为0
		assert (p->attached_threads == 0);
		if (p == arena)
		{
			//当找到对应的arena时，将前一个arena的next_free域指针修改为此arena的next_free指针
			*previous = p->next_free;
			break;
		}
		else
			//将previous修改为当前arena(p)的next_free域的指针
			previous = &p->next_free;
	}
}

/*  
	Lock and return an arena that can be reused for memory allocation.
	Avoid AVOID_ARENA as we have already failed to allocate memory in
	it and it is currently locked.	
*/
//若在free list中找到了成功加锁的arena，则调整相关参数后使用其
//若没有找到，则等待main_arena可以加锁后完成加锁
static mstate
reused_arena (mstate avoid_arena)
{
	mstate result;
	static mstate next_to_use;
	//若是第一次运行reused_arena()
	if (next_to_use == NULL)
		next_to_use = &main_arena;

	//通过next指针组成的arena循环链表，从main arena开始遍历所有arena
	result = next_to_use;
	do
	{
		//若遇到可以成功加锁的arena，则跳转到out
		if (!__libc_lock_trylock (result->mutex))
			goto out;
		/* FIXME: This is a data race, see _int_new_arena.	*/
		result = result->next;
	}
	while (result != next_to_use);
	//此处为所有arena均未加锁成功
	/* Avoid AVOID_ARENA as we have already failed to allocate memory
		 in that arena and it is currently locked.	 */
	//若next_to_use为avoid_arena，则result指针指向其next
	if (result == avoid_arena)
		result = result->next;

	//等待result指向的arena可用后，再对此arena进行加锁
	LIBC_PROBE (memory_arena_reuse_wait, 3, &result->mutex, result, avoid_arena);
	//对result指向的arena加锁
	__libc_lock_lock (result->mutex);

//获取到了可用的arena
out:
	/* Attach the arena to the current thread.	*/
	{
		//替换该thread当前绑定的arena
		mstate replaced_arena = thread_arena;
		__libc_lock_lock (free_list_lock);
		//改变当前绑定此arena的thread数量
		//!绑定并非意味着正在被使用。同一个arena同一时间仅能处理一个thread的请求
		detach_arena (replaced_arena);

		/* We may have picked up an arena on the free list.	We need to
			preserve the invariant that no arena on the free list has a
			positive attached_threads counter (otherwise,
			arena_thread_freeres cannot use the counter to determine if the
			arena needs to be put on the free list).	We unconditionally
			remove the selected arena from the free list.	The caller of
			reused_arena checked the free list and observed it to be empty,
			so the list is very short.	*/
		//若result指向的arena在free_list中，则将其从free_list中remove出来
		//*之前get_free_list函数表明，当时free_list值为Null
		//*若没有arena加入free_list,则当前free_list值仍为Null,无需remove，直接返回
			//*此种情况下，result是指向其他线程的thread_arena,且该线程未结束。但arena当前未在使用
		//*若从get_free_list到该函数中间过程中存在arena加入free_list，则result获取到的arena有可能在free_list中
			//*此中情况下，result是某个已结束的线程的arena。线程结束时该arena被清空attached_thread域并放入free_list中
			//*此时可以顺利的将result指向的arena从free_list中移除
		remove_from_free_list (result);

		++result->attached_threads;
		__libc_lock_unlock (free_list_lock);
	}

	LIBC_PROBE (memory_arena_reuse, 2, result, avoid_arena);
	thread_arena = result;
	//保存当前遍历到的位置
	next_to_use = result->next;

	return result;
}

static mstate
arena_get2 (size_t size, mstate avoid_arena)
{
	mstate a;
	//arenas数量上限
	static size_t narenas_limit;
	//获取free_list指针指向的arena，并将free_list指针指向arena free list中的下一个arena
	a = get_free_list ();
	//若获取到的arena为arena free list中的最后一个arena
	if (a == NULL)
	{
		//若未设置arenas数量上限，则设置
		if (narenas_limit == 0)
		{
			//arena_max设置，则arena_test无效，以arena_max为准
			if (mp_.arena_max != 0)
				narenas_limit = mp_.arena_max;
			//若:1.当前arena数量大于arena_test中限制的arena数
			//   2.且arena_max为0
			//则通过处理器位数和核心数计算最高arena数
			else if (narenas > mp_.arena_test)
			{
				int n = __get_nprocs ();
				//获取到n，则按n计算
				if (n >= 1)
					narenas_limit = NARENAS_FROM_NCORES (n);
				//获取不到n，按2核计算
				else
					/* We have no information about the system.	Assume two
						cores.	*/
					narenas_limit = NARENAS_FROM_NCORES (2);
			}
		}

	repeat:;
		size_t n = narenas;
		/* NB: the following depends on the fact that (size_t)0 - 1 is a
			very large number and that the underflow is OK.	If arena_max
			is set the value of arena_test is irrelevant.	If arena_test
			is set but narenas is not yet larger or equal to arena_test
			narenas_limit is 0.	There is no possibility for narenas to
			be too big for the test to always fail since there is not
			enough address space to create that many arenas.	*/
		//当现有的arena数量未超过arena数量限制时，优先考虑建立新的arena而非arena复用
		if (__glibc_unlikely (n <= narenas_limit - 1))
		{
			//原子操作，对arena数量参数加1，若失败，则重新操作
			if (catomic_compare_and_exchange_bool_acq (&narenas, n + 1, n))
				goto repeat;
			//将新建的arena加入到main arena的next指针指向的位置
			//未操作next_free指针
			a = _int_new_arena (size);
			//若创建新的arena失败则对arena数量-1(恢复之前的状态)
			if (__glibc_unlikely (a == NULL))
				catomic_decrement (&narenas);
		}
		//若已有的arena数量已经达到了上限，则考虑对arena进行复用
		else
			//遍历free list，找到可用的 / 等待某个arena直到其可用
			a = reused_arena (avoid_arena);
	}
	return a;
}

/* If we don't have the main arena, then maybe the failure is due to running
	out of mmapped areas, so we can try allocating on the main arena.
	Otherwise, it is likely that sbrk() has failed and there is still a chance
	to mmap(), so try one of the other arenas.	*/
static mstate
arena_get_retry (mstate ar_ptr, size_t bytes)
{
	LIBC_PROBE (memory_arena_retry, 2, bytes, ar_ptr);
	//若不为main arena，则对当前分配区解锁后对main arena加锁使用
	if (ar_ptr != &main_arena)
	{
		__libc_lock_unlock (ar_ptr->mutex);
		ar_ptr = &main_arena;
		__libc_lock_lock (ar_ptr->mutex);
	}
	//若为main arena，则对main arena解锁，并重新获取分配区(更换thread绑定的arena)
	else
	{
		__libc_lock_unlock (ar_ptr->mutex);
		ar_ptr = arena_get2 (bytes, ar_ptr);	
	}
	return ar_ptr;
}

//当线程退出时call该function
void
__malloc_arena_thread_freeres (void)
{
	/* 
		Shut down the thread cache first.	This could deallocate data for
		the thread arena, so do this before we put the arena on the free
		list.
	*/
	tcache_thread_shutdown ();

	mstate a = thread_arena;
	thread_arena = NULL;

	if (a != NULL)
	{
		__libc_lock_lock (free_list_lock);
		/* 
			If this was the last attached thread for this arena, put the
			arena on the free list.
		*/
		assert (a->attached_threads > 0);
		if (--a->attached_threads == 0)
		{
			a->next_free = free_list;
			free_list = a;
		}
		__libc_lock_unlock (free_list_lock);
	}
}

/*
 * Local variables:
 * c-basic-offset: 2
 * End:
 */
