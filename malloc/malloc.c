/* Malloc implementation for multiple threads without lock contention.
	Copyright (C) 1996-2018 Free Software Foundation, Inc.
	This file is part of the GNU C Library.
	Contributed by Wolfram Gloger <wg@malloc.de>
	and Doug Lea <dl@cs.oswego.edu>, 2001.

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

/*
	This is a version (aka ptmalloc2) of malloc/free/realloc written by
	Doug Lea and adapted to multiple threads/arenas by Wolfram Gloger.

	There have been substantial changes made after the integration into
	glibc in all parts of the code.	Do not look for much commonality
	with the ptmalloc2 version.

* Version ptmalloc2-20011215
	based on:
	VERSION 2.7.0 Sun Mar 11 14:14:06 2001	Doug Lea	(dl at gee)

* Quickstart

	In order to compile this implementation, a Makefile is provided with
	the ptmalloc2 distribution, which has pre-defined targets for some
	popular systems (e.g. "make posix" for Posix threads).	All that is
	typically required with regard to compiler flags is the selection of
	the thread package via defining one out of USE_PTHREADS, USE_THR or
	USE_SPROC.	Check the thread-m.h file for what effects this has.
	Many/most systems will additionally require USE_TSD_DATA_HACK to be
	defined, so this is the default for "make posix".

* Why use this malloc?

	This is not the fastest, most space-conserving, most portable, or
	most tunable malloc ever written. However it is among the fastest
	while also being among the most space-conserving, portable and tunable.
	Consistent balance across these factors results in a good general-purpose
	allocator for malloc-intensive programs.

	The main properties of the algorithms are:
	* For large (>= 512 bytes) requests, it is a pure best-fit allocator,
		with ties normally decided via FIFO (i.e. least recently used).
	* For small (<= 64 bytes by default) requests, it is a caching
		allocator, that maintains pools of quickly recycled chunks.
	* In between, and for combinations of large and small requests, it does
		the best it can trying to meet both goals at once.
	* For very large requests (>= 128KB by default), it relies on system
		memory mapping facilities, if supported.

	For a longer but slightly out of date high-level description, see
		http://gee.cs.oswego.edu/dl/html/malloc.html

	You may already by default be using a C library containing a malloc
	that is	based on some version of this malloc (for example in
	linux). You might still want to use the one in this file in order to
	customize settings or to avoid overheads associated with library
	versions.

* Contents, described in more detail in "description of public routines" below.

	Standard (ANSI/SVID/...)	functions:
		malloc(size_t n);
		calloc(size_t n_elements, size_t element_size);
		free(void* p);
		realloc(void* p, size_t n);
		memalign(size_t alignment, size_t n);
		valloc(size_t n);
		mallinfo()
		mallopt(int parameter_number, int parameter_value)

	Additional functions:
		independent_calloc(size_t n_elements, size_t size, void* chunks[]);
		independent_comalloc(size_t n_elements, size_t sizes[], void* chunks[]);
		pvalloc(size_t n);
		malloc_trim(size_t pad);
		malloc_usable_size(void* p);
		malloc_stats();

* Vital statistics:

	Supported pointer representation:			4 or 8 bytes
	Supported size_t	representation:			4 or 8 bytes
			Note that size_t is allowed to be 4 bytes even if pointers are 8.
		   You can adjust this by defining INTERNAL_SIZE_T

	Alignment:															2 * sizeof(size_t) (default)
			(i.e., 8 byte alignment with 4byte size_t). This suffices for
		   nearly all current machines and C compilers. However, you can
			define MALLOC_ALIGNMENT to be wider than this if necessary.

	Minimum overhead per allocated chunk:	4 or 8 bytes
			Each malloced chunk has a hidden word of overhead holding size
			and status information.

	Minimum allocated size: 4-byte ptrs:	16 bytes		(including 4 overhead)
				8-byte ptrs:	24/32 bytes (including, 4/8 overhead)

			When a chunk is freed, 12 (for 4byte ptrs) or 20 (for 8 byte
			ptrs but 4 byte size) or 24 (for 8/8) additional bytes are
			needed; 4 (8) for a trailing size field and 8 (16) bytes for
			free list pointers. Thus, the minimum allocatable size is
			16/24/32 bytes.

			Even a request for zero bytes (i.e., malloc(0)) returns a
			pointer to something of the minimum allocatable size.
            
			The maximum overhead wastage (i.e., number of extra bytes
			allocated than were requested in malloc) is less than or equal
			to the minimum size, except for requests >= mmap_threshold that
			are serviced via mmap(), where the worst case wastage is 2 *
			sizeof(size_t) bytes plus the remainder from a system page (the
			minimal mmap unit); typically 4096 or 8192 bytes.

	Maximum allocated size:	4-byte size_t: 2^32 minus about two pages
				8-byte size_t: 2^64 minus about two pages

			It is assumed that (possibly signed) size_t values suffice to
			represent chunk sizes. `Possibly signed' is due to the fact
			that `size_t' may be defined on a system as either a signed or
			an unsigned type. The ISO C standard says that it must be
			unsigned, but a few systems are known not to adhere to this.
			Additionally, even when size_t is unsigned, sbrk (which is by
			default used to obtain memory from system) accepts signed
			arguments, and may not be able to handle size_t-wide arguments
			with negative sign bit.	Generally, values that would
			appear as negative after accounting for overhead and alignment
			are supported only via mmap(), which does not have this
			limitation.
            
			Requests for sizes outside the allowed range will perform an optional
			failure action and then return null. (Requests may also
			also fail because a system is out of memory.)

	Thread-safety: thread-safe

	Compliance: I believe it is compliant with the 1997 Single Unix Specification
			Also SVID/XPG, ANSI C, and probably others as well.

* Synopsis of compile-time options:

		People have reported using previous versions of this malloc on all
		versions of Unix, sometimes by tweaking some of the defines
		below. It has been tested most extensively on Solaris and Linux.
		People also report using it in stand-alone embedded systems.

		The implementation is in straight, hand-tuned ANSI C.	It is not
		at all modular. (Sorry!)	It uses a lot of macros.	To be at all
		usable, this code should be compiled using an optimizing compiler
		(for example gcc -O3) that can simplify expressions and control
		paths. (FAQ: some macros import variables as arguments rather than
		declare locals because people reported that some debuggers
		otherwise get confused.)

		OPTION										DEFAULT VALUE

		Compilation Environment options:

		HAVE_MREMAP								0

		Changing default word sizes:

		INTERNAL_SIZE_T						size_t

		Configuration and functionality options:

		USE_PUBLIC_MALLOC_WRAPPERS NOT defined
		USE_MALLOC_LOCK						NOT defined
		MALLOC_DEBUG							NOT defined
		REALLOC_ZERO_BYTES_FREES	1
		TRIM_FASTBINS							0

		Options for customizing MORECORE:

		MORECORE									sbrk
		MORECORE_FAILURE					-1
		MORECORE_CONTIGUOUS				1
		MORECORE_CANNOT_TRIM			NOT defined
		MORECORE_CLEARS						1
		MMAP_AS_MORECORE_SIZE			(1024 * 1024)

		Tuning options that are also dynamically changeable via mallopt:

		DEFAULT_MXFAST						64 (for 32bit), 128 (for 64bit)
		DEFAULT_TRIM_THRESHOLD		128 * 1024
		DEFAULT_TOP_PAD						0
		DEFAULT_MMAP_THRESHOLD		128 * 1024
		DEFAULT_MMAP_MAX					65536

		There are several other #defined constants and macros that you
		probably don't want to touch unless you are extending or adapting malloc.	*/

/*
	void* is the pointer type that malloc should say it returns
*/

#ifndef void
#define void			void
#endif /*void*/

#include <stddef.h>	/* for size_t */
#include <stdlib.h>	/* for getenv(), abort() */
#include <unistd.h>	/* for __libc_enable_secure */

#include <atomic.h>
#include <_itoa.h>
#include <bits/wordsize.h>
#include <sys/sysinfo.h>

#include <ldsodefs.h>

#include <unistd.h>
#include <stdio.h>		/* needed for malloc_stats */
#include <errno.h>
#include <assert.h>

#include <shlib-compat.h>

/* For uintptr_t.	*/
#include <stdint.h>

/* For va_arg, va_start, va_end.	*/
#include <stdarg.h>

/* For MIN, MAX, powerof2.	*/
#include <sys/param.h>

/* For ALIGN_UP et. al.	*/
#include <libc-pointer-arith.h>

/* For DIAG_PUSH/POP_NEEDS_COMMENT et al.	*/
#include <libc-diag.h>

#include <malloc/malloc-internal.h>

/* For SINGLE_THREAD_P.	*/
#include <sysdep-cancel.h>

/*
	Debugging:

	Because freed chunks may be overwritten with bookkeeping fields, this
	malloc will often die when freed memory is overwritten by user
	programs.	This can be very effective (albeit in an annoying way)
	in helping track down dangling pointers.

	If you compile with -DMALLOC_DEBUG, a number of assertion checks are
	enabled that will catch more memory errors. You probably won't be
	able to make much sense of the actual assertion errors, but they
	should help you locate incorrectly overwritten memory.	The checking
	is fairly extensive, and will slow down execution
	noticeably. Calling malloc_stats or mallinfo with MALLOC_DEBUG set
	will attempt to check every non-mmapped allocated and free chunk in
	the course of computing the summmaries. (By nature, mmapped regions
	cannot be checked very much automatically.)

	Setting MALLOC_DEBUG may also be helpful if you are trying to modify
	this code. The assertions in the check routines spell out in more
	detail the assumptions and invariants underlying the algorithms.

	Setting MALLOC_DEBUG does NOT provide an automated mechanism for
	checking that all accesses to malloced memory stay within their
	bounds. However, there are several add-ons and adaptations of this
	or other mallocs available that do this.
*/

#ifndef MALLOC_DEBUG
#define MALLOC_DEBUG 0
#endif

#ifndef NDEBUG
# define __assert_fail(assertion, file, line, function)			\
	__malloc_assert(assertion, file, line, function)

extern const char *__progname;

static void
__malloc_assert (const char *assertion, const char *file, unsigned int line,
		const char *function)
{
	(void) __fxprintf (NULL, "%s%s%s:%u: %s%sAssertion `%s' failed.\n",
				__progname, __progname[0] ? ": " : "",
				file, line,
				function ? function : "", function ? ": " : "",
				assertion);
	fflush (stderr);
	abort ();
}
#endif

//#if USE_TCACHE																		//此处注释了宏的条件便于查看交叉引用
/* We want 64 entries.	This is an arbitrary limit, which tunables can reduce.	*/
# define TCACHE_MAX_BINS		64
# define MAX_TCACHE_SIZE	tidx2usize (TCACHE_MAX_BINS-1)

/* Only used to pre-fill the tunables.	*/
# define tidx2usize(idx)	(((size_t) idx) * MALLOC_ALIGNMENT + MINSIZE - SIZE_SZ)

/* When "x" is from chunksize().	
此处x为requests_size相对应的chunk_size
对于tcache size，将普通的chunk大小减去了前四个固定字段，并且做向上对齐
MINSIZE为普通chunk(除large chunk以外)的最小大小，即从chunk头到bck_ptr指针处
MALLOC_ALIGNMENT - 1后 / MALLOC_ALIGNMENT包含有向上对齐操作
此处可看出tcache的大小为requests大小向上对其到2 * SIZE_SZ,即使用时没有其他固有结构存在
*/
# define csize2tidx(x) (((x) - MINSIZE + MALLOC_ALIGNMENT - 1) / MALLOC_ALIGNMENT)

/* When "x" is a user-provided size.	*/												
# define usize2tidx(x) csize2tidx (request2size (x))

/* With rounding and alignment, the bins are...
	idx 0	bytes 0..24 (64-bit) or 0..12 (32-bit)
	idx 1	bytes 25..40 or 13..20
	idx 2	bytes 41..56 or 21..28
	etc.	*/

/* This is another arbitrary limit, which tunables can change.	Each
	tcache bin will hold at most this number of chunks.	*/
	//每个tcache bucket中默认最多维持7个tcache
# define TCACHE_FILL_COUNT 7
//#endif


/*
	REALLOC_ZERO_BYTES_FREES should be set if a call to
	realloc with zero bytes should be the same as a call to free.
	This is required by the C standard. Otherwise, since this malloc
	returns a unique pointer for malloc(0), so does realloc(p, 0).
*/

#ifndef REALLOC_ZERO_BYTES_FREES
#define REALLOC_ZERO_BYTES_FREES 1
#endif

/*
	TRIM_FASTBINS controls whether free() of a very small chunk can
	immediately lead to trimming. Setting to true (1) can reduce memory
	footprint, but will almost always slow down programs that use a lot
	of small chunks.

	Define this only if you are willing to give up some speed to more
	aggressively reduce system-level memory footprint when releasing
	memory in programs that use many small chunks.	You can get
	essentially the same effect by setting MXFAST to 0, but this can
	lead to even greater slowdowns in programs using many small chunks.
	TRIM_FASTBINS is an in-between compile-time option, that disables
	only those chunks bordering topmost memory from being placed in
	fastbins.
*/

#ifndef TRIM_FASTBINS
#define TRIM_FASTBINS	0
#endif


/* Definition for getting more memory from the OS.	*/
#define MORECORE				(*__morecore)
#define MORECORE_FAILURE 0
void * __default_morecore (ptrdiff_t);
void *(*__morecore)(ptrdiff_t) = __default_morecore;


#include <string.h>

/*
	MORECORE-related declarations. By default, rely on sbrk
*/


/*
	MORECORE is the name of the routine to call to obtain more memory
	from the system.	See below for general guidance on writing
	alternative MORECORE functions, as well as a version for WIN32 and a
	sample version for pre-OSX macos.
*/

#ifndef MORECORE
#define MORECORE sbrk
#endif

/*
	MORECORE_FAILURE is the value returned upon failure of MORECORE
	as well as mmap. Since it cannot be an otherwise valid memory address,
	and must reflect values of standard sys calls, you probably ought not
	try to redefine it.
*/

#ifndef MORECORE_FAILURE
#define MORECORE_FAILURE (-1)
#endif

/*
	If MORECORE_CONTIGUOUS is true, take advantage of fact that
	consecutive calls to MORECORE with positive arguments always return
	contiguous increasing addresses.	This is true of unix sbrk.	Even
	if not defined, when regions happen to be contiguous, malloc will
	permit allocations spanning regions obtained from different
	calls. But defining this when applicable enables some stronger
	consistency checks and space efficiencies.
*/

#ifndef MORECORE_CONTIGUOUS
#define MORECORE_CONTIGUOUS 1
#endif

/*
	Define MORECORE_CANNOT_TRIM if your version of MORECORE
	cannot release space back to the system when given negative
	arguments. This is generally necessary only if you are using
	a hand-crafted MORECORE function that cannot handle negative arguments.
*/

/* #define MORECORE_CANNOT_TRIM */

/*	MORECORE_CLEARS					(default 1)
		The degree to which the routine mapped to MORECORE zeroes out
		memory: never (0), only for newly allocated space (1) or always
		(2).	The distinction between (1) and (2) is necessary because on
		some systems, if the application first decrements and then
		increments the break value, the contents of the reallocated space
		are unspecified.
 */

#ifndef MORECORE_CLEARS
# define MORECORE_CLEARS 1
#endif


/*
	MMAP_AS_MORECORE_SIZE is the minimum mmap size argument to use if
	sbrk fails, and mmap is used as a backup.	The value must be a
	multiple of page size.	This backup strategy generally applies only
	when systems have "holes" in address space, so sbrk cannot perform
	contiguous expansion, but there is still space available on system.
	On systems for which this is known to be useful (i.e. most linux
	kernels), this occurs only when programs allocate huge amounts of
	memory.	Between this, and the fact that mmap regions tend to be
	limited, the size should be large, to avoid too many mmap calls and
	thus avoid running out of kernel resources.	*/

#ifndef MMAP_AS_MORECORE_SIZE
#define MMAP_AS_MORECORE_SIZE (1024 * 1024)
#endif

/*
	Define HAVE_MREMAP to make realloc() use mremap() to re-allocate
	large blocks.
*/

#ifndef HAVE_MREMAP
#define HAVE_MREMAP 0
#endif

/* We may need to support __malloc_initialize_hook for backwards
	compatibility.	*/

#if SHLIB_COMPAT (libc, GLIBC_2_0, GLIBC_2_24)
# define HAVE_MALLOC_INIT_HOOK 1
#else
# define HAVE_MALLOC_INIT_HOOK 0
#endif


/*
	This version of malloc supports the standard SVID/XPG mallinfo
	routine that returns a struct containing usage properties and
	statistics. It should work on any SVID/XPG compliant system that has
	a /usr/include/malloc.h defining struct mallinfo. (If you'd like to
	install such a thing yourself, cut out the preliminary declarations
	as described above and below and save them in a malloc.h file. But
	there's no compelling reason to bother to do this.)

	The main declaration needed is the mallinfo struct that is returned
	(by-copy) by mallinfo().	The SVID/XPG malloinfo struct contains a
	bunch of fields that are not even meaningful in this version of
	malloc.	These fields are are instead filled by mallinfo() with
	other numbers that might be of interest.
*/


/* ---------- description of public routines ------------ */

/*
	malloc(size_t n)
	Returns a pointer to a newly allocated chunk of at least n bytes, or null
	if no space is available. Additionally, on failure, errno is
	set to ENOMEM on ANSI C systems.

	If n is zero, malloc returns a minumum-sized chunk. (The minimum
	size is 16 bytes on most 32bit systems, and 24 or 32 bytes on 64bit
	systems.)	On most systems, size_t is an unsigned type, so calls
	with negative arguments are interpreted as requests for huge amounts
	of space, which will often fail. The maximum supported value of n
	differs across systems, but is in all cases less than the maximum
	representable value of a size_t.
*/
void*	__libc_malloc(size_t);
libc_hidden_proto (__libc_malloc)

/*
	free(void* p)
	Releases the chunk of memory pointed to by p, that had been previously
	allocated using malloc or a related routine such as realloc.
	It has no effect if p is null. It can have arbitrary (i.e., bad!)
	effects if p has already been freed.

	Unless disabled (using mallopt), freeing very large spaces will
	when possible, automatically trigger operations that give
	back unused memory to the system, thus reducing program footprint.
*/
void		__libc_free(void*);
libc_hidden_proto (__libc_free)

/*
	calloc(size_t n_elements, size_t element_size);
	Returns a pointer to n_elements * element_size bytes, with all locations
	set to zero.
*/
void*	__libc_calloc(size_t, size_t);

/*
	realloc(void* p, size_t n)
	Returns a pointer to a chunk of size n that contains the same data
	as does chunk p up to the minimum of (n, p's size) bytes, or null
	if no space is available.

	The returned pointer may or may not be the same as p. The algorithm
	prefers extending p when possible, otherwise it employs the
	equivalent of a malloc-copy-free sequence.

	If p is null, realloc is equivalent to malloc.

	If space is not available, realloc returns null, errno is set (if on
	ANSI) and p is NOT freed.

	if n is for fewer bytes than already held by p, the newly unused
	space is lopped off and freed if possible.	Unless the #define
	REALLOC_ZERO_BYTES_FREES is set, realloc with a size argument of
	zero (re)allocates a minimum-sized chunk.

	Large chunks that were internally obtained via mmap will always be
	grown using malloc-copy-free sequences unless the system supports
	MREMAP (currently only linux).

	The old unix realloc convention of allowing the last-free'd chunk
	to be used as an argument to realloc is not supported.
*/
void*	__libc_realloc(void*, size_t);
libc_hidden_proto (__libc_realloc)

/*
	memalign(size_t alignment, size_t n);
	Returns a pointer to a newly allocated chunk of n bytes, aligned
	in accord with the alignment argument.

	The alignment argument should be a power of two. If the argument is
	not a power of two, the nearest greater power is used.
	8-byte alignment is guaranteed by normal malloc calls, so don't
	bother calling memalign with an argument of 8 or less.

	Overreliance on memalign is a sure way to fragment space.
*/
void*	__libc_memalign(size_t, size_t);
libc_hidden_proto (__libc_memalign)

/*
	valloc(size_t n);
	Equivalent to memalign(pagesize, n), where pagesize is the page
	size of the system. If the pagesize is unknown, 4096 is used.
*/
void*	__libc_valloc(size_t);



/*
	mallopt(int parameter_number, int parameter_value)
	Sets tunable parameters The format is to provide a
	(parameter-number, parameter-value) pair.	mallopt then sets the
	corresponding parameter to the argument value if it can (i.e., so
	long as the value is meaningful), and returns 1 if successful else
	0.	SVID/XPG/ANSI defines four standard param numbers for mallopt,
	normally defined in malloc.h.	Only one of these (M_MXFAST) is used
	in this malloc. The others (M_NLBLKS, M_GRAIN, M_KEEP) don't apply,
	so setting them has no effect. But this malloc also supports four
	other options in mallopt. See below for details.	Briefly, supported
	parameters are as follows (listed defaults are for "typical"
	configurations).

	Symbol						param #	default		allowed param values
	M_MXFAST					1				64				0-80	(0 disables fastbins)
	M_TRIM_THRESHOLD -1				128*1024	any	(-1U disables trimming)
	M_TOP_PAD				-2				0					any
	M_MMAP_THRESHOLD -3				128*1024	any	(or 0 if no MMAP support)
	M_MMAP_MAX			-4				65536			any	(0 disables use of mmap)
*/
int			__libc_mallopt(int, int);
libc_hidden_proto (__libc_mallopt)


/*
	mallinfo()
	Returns (by copy) a struct containing various summary statistics:

	arena:		current total non-mmapped bytes allocated from system
	ordblks:	the number of free chunks
	smblks:		the number of fastbin blocks (i.e., small chunks that
				have been freed but not use resused or consolidated)
	hblks:		current number of mmapped regions
	hblkhd:		total bytes held in mmapped regions
	usmblks:	always 0
	fsmblks:	total bytes held in fastbin blocks
	uordblks:	current total allocated space (normal or mmapped)
	fordblks:	total free space
	keepcost:	the maximum number of bytes that could ideally be released
				back to system via malloc_trim. ("ideally" means that
				it ignores page restrictions etc.)

	Because these fields are ints, but internal bookkeeping may
	be kept as longs, the reported values may wrap around zero and
	thus be inaccurate.
*/
struct mallinfo __libc_mallinfo(void);


/*
	pvalloc(size_t n);
	Equivalent to valloc(minimum-page-that-holds(n)), that is,
	round up n to nearest pagesize.
 */
void*	__libc_pvalloc(size_t);

/*
	malloc_trim(size_t pad);

	If possible, gives memory back to the system (via negative
	arguments to sbrk) if there is unused memory at the `high' end of
	the malloc pool. You can call this after freeing large blocks of
	memory to potentially reduce the system-level memory requirements
	of a program. However, it cannot guarantee to reduce memory. Under
	some allocation patterns, some large free blocks of memory will be
	locked between two used chunks, so they cannot be given back to
	the system.

	The `pad' argument to malloc_trim represents the amount of free
	trailing space to leave untrimmed. If this argument is zero,
	only the minimum amount of memory to maintain internal data
	structures will be left (one page or less). Non-zero arguments
	can be supplied to maintain enough trailing space to service
	future expected allocations without having to re-obtain memory
	from the system.

	Malloc_trim returns 1 if it actually released any memory, else 0.
	On systems that do not support "negative sbrks", it will always
	return 0.
*/
int			__malloc_trim(size_t);

/*
	malloc_usable_size(void* p);

	Returns the number of bytes you can actually use in
	an allocated chunk, which may be more than you requested (although
	often not) due to alignment and minimum size constraints.
	You can use this many bytes without worrying about
	overwriting other allocated objects. This is not a particularly great
	programming practice. malloc_usable_size can be more useful in
	debugging and assertions, for example:

	p = malloc(n);
	assert(malloc_usable_size(p) >= 256);

*/
size_t	__malloc_usable_size(void*);

/*
	malloc_stats();
	Prints on stderr the amount of space obtained from the system (both
	via sbrk and mmap), the maximum amount (which may be more than
	current if malloc_trim and/or munmap got called), and the current
	number of bytes allocated via malloc (or realloc, etc) but not yet
	freed. Note that this is the number of bytes allocated, not the
	number requested. It will be larger than the number requested
	because of alignment and bookkeeping overhead. Because it includes
	alignment wastage as being in use, this figure may be greater than
	zero even when no user-level chunks are allocated.

	The reported current and maximum system memory can be inaccurate if
	a program makes other calls to system memory allocation functions
	(normally sbrk) outside of malloc.

	malloc_stats prints only the most commonly interesting statistics.
	More information can be obtained by calling mallinfo.

*/
void		__malloc_stats(void);

/*
	posix_memalign(void **memptr, size_t alignment, size_t size);

	POSIX wrapper like memalign(), checking for validity of size.
*/
int			__posix_memalign(void **, size_t, size_t);

/* mallopt tuning options */

/*
	M_MXFAST is the maximum request size used for "fastbins", special bins
	that hold returned chunks without consolidating their spaces. This
	enables future requests for chunks of the same size to be handled
	very quickly, but can increase fragmentation, and thus increase the
	overall memory footprint of a program.

	This malloc manages fastbins very conservatively yet still
	efficiently, so fragmentation is rarely a problem for values less
	than or equal to the default.	The maximum supported value of MXFAST
	is 80. You wouldn't want it any higher than this anyway.	Fastbins
	are designed especially for use with many small structs, objects or
	strings -- the default handles structs/objects/arrays with sizes up
	to 8 4byte fields, or small strings representing words, tokens,
	etc. Using fastbins for larger objects normally worsens
	fragmentation without improving speed.

	M_MXFAST is set in REQUEST size units. It is internally used in
	chunksize units, which adds padding and alignment.	You can reduce
	M_MXFAST to 0 to disable all use of fastbins.	This causes the malloc
	algorithm to be a closer approximation of fifo-best-fit in all cases,
	not just for larger requests, but will generally cause it to be
	slower.
*/


/* M_MXFAST is a standard SVID/XPG tuning option, usually listed in malloc.h */
#ifndef M_MXFAST
#define M_MXFAST						1
#endif

#ifndef DEFAULT_MXFAST
#define DEFAULT_MXFAST		(64 * SIZE_SZ / 4)
#endif


/*
	M_TRIM_THRESHOLD is the maximum amount of unused top-most memory
	to keep before releasing via malloc_trim in free().

	Automatic trimming is mainly useful in long-lived programs.
	Because trimming via sbrk can be slow on some systems, and can
	sometimes be wasteful (in cases where programs immediately
	afterward allocate more large chunks) the value should be high
	enough so that your overall system performance would improve by
	releasing this much memory.

	The trim threshold and the mmap control parameters (see below)
	can be traded off with one another. Trimming and mmapping are
	two different ways of releasing unused memory back to the
	system. Between these two, it is often possible to keep
	system-level demands of a long-lived program down to a bare
	minimum. For example, in one test suite of sessions measuring
	the XF86 X server on Linux, using a trim threshold of 128K and a
	mmap threshold of 192K led to near-minimal long term resource
	consumption.

	If you are using this malloc in a long-lived program, it should
	pay to experiment with these values.	As a rough guide, you
	might set to a value close to the average size of a process
	(program) running on your system.	Releasing this much memory
	would allow such a process to run in memory.	Generally, it's
	worth it to tune for trimming rather tham memory mapping when a
	program undergoes phases where several large chunks are
	allocated and released in ways that can reuse each other's
	storage, perhaps mixed with phases where there are no such
	chunks at all.	And in well-behaved long-lived programs,
	controlling release of large blocks via trimming versus mapping
	is usually faster.

	However, in most programs, these parameters serve mainly as
	protection against the system-level effects of carrying around
	massive amounts of unneeded memory. Since frequent calls to
	sbrk, mmap, and munmap otherwise degrade performance, the default
	parameters are set to relatively high values that serve only as
	safeguards.

	The trim value It must be greater than page size to have any useful
	effect.	To disable trimming completely, you can set to
	(unsigned long)(-1)

	Trim settings interact with fastbin (MXFAST) settings: Unless
	TRIM_FASTBINS is defined, automatic trimming never takes place upon
	freeing a chunk with size less than or equal to MXFAST. Trimming is
	instead delayed until subsequent freeing of larger chunks. However,
	you can still force an attempted trim by calling malloc_trim.

	Also, trimming is not generally possible in cases where
	the main arena is obtained via mmap.

	Note that the trick some people use of mallocing a huge space and
	then freeing it at program startup, in an attempt to reserve system
	memory, doesn't have the intended effect under automatic trimming,
	since that memory will immediately be returned to the system.
*/

#define M_TRIM_THRESHOLD			-1

#ifndef DEFAULT_TRIM_THRESHOLD
#define DEFAULT_TRIM_THRESHOLD (128 * 1024)
#endif

/*
	M_TOP_PAD is the amount of extra `padding' space to allocate or
	retain whenever sbrk is called. It is used in two ways internally:

	* When sbrk is called to extend the top of the arena to satisfy
	a new malloc request, this much padding is added to the sbrk
	request.

	* When malloc_trim is called automatically from free(),
	it is used as the `pad' argument.

	In both cases, the actual amount of padding is rounded
	so that the end of the arena is always a system page boundary.

	The main reason for using padding is to avoid calling sbrk so
	often. Having even a small pad greatly reduces the likelihood
	that nearly every malloc request during program start-up (or
	after trimming) will invoke sbrk, which needlessly wastes
	time.

	Automatic rounding-up to page-size units is normally sufficient
	to avoid measurable overhead, so the default is 0.	However, in
	systems where sbrk is relatively slow, it can pay to increase
	this value, at the expense of carrying around more memory than
	the program needs.
*/

#define M_TOP_PAD							-2

#ifndef DEFAULT_TOP_PAD
#define DEFAULT_TOP_PAD				(0)
#endif

/*
	MMAP_THRESHOLD_MAX and _MIN are the bounds on the dynamically
	adjusted MMAP_THRESHOLD.
*/

#ifndef DEFAULT_MMAP_THRESHOLD_MIN
#define DEFAULT_MMAP_THRESHOLD_MIN (128 * 1024)
#endif

#ifndef DEFAULT_MMAP_THRESHOLD_MAX
	/* For 32-bit platforms we cannot increase the maximum mmap
		threshold much because it is also the minimum value for the
		maximum heap size and its alignment.	Going above 512k (i.e., 1M
		for new heaps) wastes too much address space.	*/
# if __WORDSIZE == 32
#	define DEFAULT_MMAP_THRESHOLD_MAX (512 * 1024)
# else
#	define DEFAULT_MMAP_THRESHOLD_MAX (4 * 1024 * 1024 * sizeof(long))
# endif
#endif

/*
	M_MMAP_THRESHOLD is the request size threshold for using mmap()
	to service a request. Requests of at least this size that cannot
	be allocated using already-existing space will be serviced via mmap.
	(If enough normal freed space already exists it is used instead.)

	Using mmap segregates relatively large chunks of memory so that
	they can be individually obtained and released from the host
	system. A request serviced through mmap is never reused by any
	other request (at least not directly; the system may just so
	happen to remap successive requests to the same locations).

	Segregating space in this way has the benefits that:

	1. Mmapped space can ALWAYS be individually released back
			to the system, which helps keep the system level memory
			demands of a long-lived program low.
	2. Mapped memory can never become `locked' between
			other chunks, as can happen with normally allocated chunks, which
			means that even trimming via malloc_trim would not release them.
	3. On some systems with "holes" in address spaces, mmap can obtain
			memory that sbrk cannot.

	However, it has the disadvantages that:

	1. The space cannot be reclaimed, consolidated, and then
			used to service later requests, as happens with normal chunks.
	2. It can lead to more wastage because of mmap page alignment
			requirements
	3. It causes malloc performance to be more dependent on host
			system memory management support routines which may vary in
			implementation quality and may impose arbitrary
			limitations. Generally, servicing a request via normal
			malloc steps is faster than going through a system's mmap.

	The advantages of mmap nearly always outweigh disadvantages for
	"large" chunks, but the value of "large" varies across systems.	The
	default is an empirically derived value that works well in most
	systems.


	Update in 2006:
	The above was written in 2001. Since then the world has changed a lot.
	Memory got bigger. Applications got bigger. The virtual address space
	layout in 32 bit linux changed.

	In the new situation, brk() and mmap space is shared and there are no
	artificial limits on brk size imposed by the kernel. What is more,
	applications have started using transient allocations larger than the
	128Kb as was imagined in 2001.

	The price for mmap is also high now; each time glibc mmaps from the
	kernel, the kernel is forced to zero out the memory it gives to the
	application. Zeroing memory is expensive and eats a lot of cache and
	memory bandwidth. This has nothing to do with the efficiency of the
	virtual memory system, by doing mmap the kernel just has no choice but
	to zero.

	In 2001, the kernel had a maximum size for brk() which was about 800
	megabytes on 32 bit x86, at that point brk() would hit the first
	mmaped shared libaries and couldn't expand anymore. With current 2.6
	kernels, the VA space layout is different and brk() and mmap
	both can span the entire heap at will.

	Rather than using a static threshold for the brk/mmap tradeoff,
	we are now using a simple dynamic one. The goal is still to avoid
	fragmentation. The old goals we kept are
	1) try to get the long lived large allocations to use mmap()
	2) really large allocations should always use mmap()
	and we're adding now:
	3) transient allocations should use brk() to avoid forcing the kernel
		having to zero memory over and over again

	The implementation works with a sliding threshold, which is by default
	limited to go between 128Kb and 32Mb (64Mb for 64 bitmachines) and starts
	out at 128Kb as per the 2001 default.

	This allows us to satisfy requirement 1) under the assumption that long
	lived allocations are made early in the process' lifespan, before it has
	started doing dynamic allocations of the same size (which will
	increase the threshold).

	The upperbound on the threshold satisfies requirement 2)

	The threshold goes up in value when the application frees memory that was
	allocated with the mmap allocator. The idea is that once the application
	starts freeing memory of a certain size, it's highly probable that this is
	a size the application uses for transient allocations. This estimator
	is there to satisfy the new third requirement.

*/

#define M_MMAP_THRESHOLD			-3

#ifndef DEFAULT_MMAP_THRESHOLD
#define DEFAULT_MMAP_THRESHOLD DEFAULT_MMAP_THRESHOLD_MIN
#endif

/*
	M_MMAP_MAX is the maximum number of requests to simultaneously
	service using mmap. This parameter exists because
	some systems have a limited number of internal tables for
	use by mmap, and using more than a few of them may degrade
	performance.

	The default is set to a value that serves only as a safeguard.
	Setting to 0 disables use of mmap for servicing large requests.
*/

#define M_MMAP_MAX						-4

#ifndef DEFAULT_MMAP_MAX
#define DEFAULT_MMAP_MAX			(65536)
#endif

#include <malloc.h>

#ifndef RETURN_ADDRESS
#define RETURN_ADDRESS(X_) (NULL)
#endif

/* Forward declarations.	*/
struct malloc_chunk;
typedef struct malloc_chunk* mchunkptr;

/* Internal routines.	*/

static void *_int_malloc(mstate, size_t);
static void	_int_free(mstate, mchunkptr, int);
static void *_int_realloc(mstate, mchunkptr, INTERNAL_SIZE_T,
				INTERNAL_SIZE_T);
static void *_int_memalign(mstate, size_t, size_t);
static void *_mid_memalign(size_t, size_t, void *);

static void malloc_printerr(const char *str) __attribute__ ((noreturn));

static void *mem2mem_check(void *p, size_t sz);
static void top_check(void);
static void munmap_chunk(mchunkptr p);
#if HAVE_MREMAP
static mchunkptr mremap_chunk(mchunkptr p, size_t new_size);
#endif

static void	*malloc_check(size_t sz, const void *caller);
static void	free_check(void* mem, const void *caller);
static void *realloc_check(void* oldmem, size_t bytes,
						const void *caller);
static void *memalign_check(size_t alignment, size_t bytes,
				const void *caller);

/* ------------------ MMAP support ------------------	*/


#include <fcntl.h>
#include <sys/mman.h>

#if !defined(MAP_ANONYMOUS) && defined(MAP_ANON)
# define MAP_ANONYMOUS MAP_ANON
#endif

#ifndef MAP_NORESERVE
# define MAP_NORESERVE 0
#endif

#define MMAP(addr, size, prot, flags) \
 __mmap((addr), (size), (prot), (flags)|MAP_ANONYMOUS|MAP_PRIVATE, -1, 0)


/*
	-----------------------	Chunk representations -----------------------
*/


/*
	This struct declaration is misleading (but accurate and necessary).
	It declares a "view" into memory allowing access to necessary
	fields at known offsets from a given base. See explanation below.
*/

struct malloc_chunk {		//每个字段size均为SIZE_SZ， 32bit下为4byte， 64bit下为8byte

	INTERNAL_SIZE_T			mchunk_prev_size;	/* Size of previous chunk (if free).	*/
	INTERNAL_SIZE_T			mchunk_size;			/* Size in bytes, including overhead. */

	struct malloc_chunk* fd;				/* double links -- used only if free. */
	struct malloc_chunk* bk;

	/* Only used for large blocks: pointer to next larger size.	*/
	struct malloc_chunk* fd_nextsize; /* double links -- used only if free. */
	struct malloc_chunk* bk_nextsize;
};


/*
	malloc_chunk details:

		(The following includes lightly edited explanations by Colin Plumb.)

		Chunks of memory are maintained using a `boundary tag' method as
		described in e.g., Knuth or Standish.	(See the paper by Paul
		Wilson ftp://ftp.cs.utexas.edu/pub/garbage/allocsrv.ps for a
		survey of such techniques.)	Sizes of free chunks are stored both
		in the front of each chunk and at the end.	This makes
		consolidating fragmented chunks into bigger chunks very fast.	The
		size fields also hold bits representing whether chunks are free or
		in use.

		An allocated chunk looks like this:


	chunk-> +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|			Size of previous chunk, if unallocated (P clear)	|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|				Size of chunk, in bytes				   	  |A|M|P|
	mem->   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|				User data starts here...						.
			.																.
			.				(malloc_usable_size() bytes)					.
			.																|
nextchunk-> +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|			(size of chunk, but used for application data)		|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|			Size of next chunk, in bytes				  |A|0|1|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

		Where "chunk" is the front of the chunk for the purpose of most of
		the malloc code, but "mem" is the pointer that is returned to the
		user.	"Nextchunk" is the beginning of the next contiguous chunk.

		Chunks always begin on even word boundaries, so the mem portion
		(which is returned to the user) is also on an even word boundary, and
		thus at least double-word aligned.

		Free chunks are stored in circular doubly-linked lists, and look like this:

	chunk-> +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|			Size of previous chunk, if unallocated (P clear)	|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
	`head:' |					Size of chunk, in bytes	    	      |A|0|P|
	mem->   +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|			    Forward pointer to next chunk in list			|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|				Back pointer to previous chunk in list			|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|				Unused space (may be 0 bytes long)              .
			.														    	.
			.																|
nextchunk-> +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
		`foot:' |						Size of chunk, in bytes				|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
			|						Size of next chunk, in bytes	  |A|0|0|
			+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

		The P (PREV_INUSE) bit, stored in the unused low-order bit of the
		chunk size (which is always a multiple of two words), is an in-use
		bit for the *previous* chunk.	If that bit is *clear*, then the
		word before the current chunk size contains the previous chunk
		size, and can be used to find the front of the previous chunk.
		The very first chunk allocated always has this bit set,
		preventing access to non-existent (or non-owned) memory. If
		prev_inuse is set for any given chunk, then you CANNOT determine
		the size of the previous chunk, and might even get a memory
		addressing fault when trying to do so.

		The A (NON_MAIN_ARENA) bit is cleared for chunks on the initial,
		main arena, described by the main_arena variable.	When additional
		threads are spawned, each thread receives its own arena (up to a
		configurable limit, after which arenas are reused for multiple
		threads), and the chunks in these arenas have the A bit set.	To
		find the arena for a chunk on such a non-main arena, heap_for_ptr
		performs a bit mask operation and indirection through the ar_ptr
		member of the per-heap header heap_info (see arena.c).

		Note that the `foot' of the current chunk is actually represented
		as the prev_size of the NEXT chunk. This makes it easier to
		deal with alignments etc but can be very confusing when trying
		to extend or adapt this code.

		The three exceptions to all this are:

		1. The special chunk `top' doesn't bother using the
	trailing size field since there is no next contiguous chunk
	that would have to index off it. After initialization, `top'
	is forced to always exist.	If it would become less than
	MINSIZE bytes long, it is replenished.

		2. Chunks allocated via mmap, which have the second-lowest-order
	bit M (IS_MMAPPED) set in their size fields.	Because they are
	allocated one-by-one, each must contain its own trailing size
	field.	If the M bit is set, the other bits are ignored
	(because mmapped chunks are neither in an arena, nor adjacent
	to a freed chunk).	The M bit is also used for chunks which
	originally came from a dumped heap via malloc_set_state in
	hooks.c.

		3. Chunks in fastbins are treated as allocated chunks from the
	point of view of the chunk allocator.	They are consolidated
	with their neighbors only in bulk, in malloc_consolidate.
*/

/*
	---------- Size and alignment checks and conversions ----------
*/

/* conversion from malloc headers to user pointers, and back */

#define chunk2mem(p)	((void*)((char*)(p) + 2*SIZE_SZ))
#define mem2chunk(mem) ((mchunkptr)((char*)(mem) - 2*SIZE_SZ))  //将指针还原为chunk头指针，随后将其类型转化为标准chunk类型(mchunkptr)

/* The smallest possible chunk */
#define MIN_CHUNK_SIZE				(offsetof(struct malloc_chunk, fd_nextsize))	//最小chunk大小定义为chunk开头到fd_nextsize字段的大小，即为4个字段
																					//64bit下为32byte  32bit为16byte(4*8  4*4)

/* The smallest size we can malloc is an aligned minimal chunk */

#define MINSIZE	\
	(unsigned long)(((MIN_CHUNK_SIZE+MALLOC_ALIGN_MASK) & ~MALLOC_ALIGN_MASK))		//向上对齐chunk大小

/* Check if m has acceptable alignment */

#define aligned_OK(m)	(((unsigned long)(m) & MALLOC_ALIGN_MASK) == 0)

#define misaligned_chunk(p) \
	((uintptr_t)(MALLOC_ALIGNMENT == 2 * SIZE_SZ ? (p) : chunk2mem (p)) \
	& MALLOC_ALIGN_MASK)


/*
	Check if a request is so large that it would wrap around zero when
	padded and aligned. To simplify some other code, the bound is made
	low enough so that adding MINSIZE will also not wrap around zero.
 */

#define REQUEST_OUT_OF_RANGE(req)																\
	((unsigned long) (req) >=									\
	(unsigned long) (INTERNAL_SIZE_T) (-2 * MINSIZE))

/* pad request bytes into a usable size -- internal version */

#define request2size(req)																				\
	(((req) + SIZE_SZ + MALLOC_ALIGN_MASK < MINSIZE)	?						\
	MINSIZE :																											\
	((req) + SIZE_SZ + MALLOC_ALIGN_MASK) & ~MALLOC_ALIGN_MASK)		//需创建的chunk大小为请求大小 + SIZE_SZ(包含地址复用区域) 后向上对其SIZE_SZ

/* Same, except also perform an argument and result check.	First, we check
	that the padding done by request2size didn't result in an integer
	overflow.	Then we check (using REQUEST_OUT_OF_RANGE) that the resulting
	size isn't so large that a later alignment would lead to another integer
	overflow.	*/
#define checked_request2size(req, sz) \
({						\
	(sz) = request2size (req);			\
	if (((sz) < (req))				\
			|| REQUEST_OUT_OF_RANGE (sz)) \
		{						\
			__set_errno (ENOMEM);			\
			return 0;					\
		}						\
})
		/*
			1.将requests的地址大小转换为chunk需要的地址大小
			2.检测requests地址大小是否大于计算出的chunk大小，以及计算出的size大小是否超出范围
		*/
/*
	--------------- Physical chunk operations ---------------
 */


/* size field is or'ed with PREV_INUSE when previous adjacent chunk in use */
#define PREV_INUSE 0x1

/* extract inuse bit of previous chunk */
#define prev_inuse(p)			((p)->mchunk_size & PREV_INUSE)


/* size field is or'ed with IS_MMAPPED if the chunk was obtained with mmap() */
#define IS_MMAPPED 0x2

/* check for mmap()'ed chunk */
#define chunk_is_mmapped(p) ((p)->mchunk_size & IS_MMAPPED)


/* size field is or'ed with NON_MAIN_ARENA if the chunk was obtained
	from a non-main arena.	This is only set immediately before handing
	the chunk to the user, if necessary.	*/
#define NON_MAIN_ARENA 0x4

/* Check for chunk from main arena.	*/
#define chunk_main_arena(p) (((p)->mchunk_size & NON_MAIN_ARENA) == 0)

/* Mark a chunk as not being on the main arena.	*/
#define set_non_main_arena(p) ((p)->mchunk_size |= NON_MAIN_ARENA)


/*
	Bits to mask off when extracting size

	Note: IS_MMAPPED is intentionally not masked off from size field in
	macros for which mmapped chunks should never be seen. This should
	cause helpful core dumps to occur if it is tried by accident by
	people extending or adapting this malloc.
 */
#define SIZE_BITS (PREV_INUSE | IS_MMAPPED | NON_MAIN_ARENA)

/* Get size, ignoring use bits */
#define chunksize(p) (chunksize_nomask (p) & ~(SIZE_BITS))

/* Like chunksize, but do not mask SIZE_BITS.	*/
#define chunksize_nomask(p)				((p)->mchunk_size)

/* Ptr to next physical malloc_chunk. */
#define next_chunk(p) ((mchunkptr) (((char *) (p)) + chunksize (p)))

/* Size of the chunk below P.	Only valid if !prev_inuse (P).	*/
#define prev_size(p) ((p)->mchunk_prev_size)

/* Set the size of the chunk below P.	Only valid if !prev_inuse (P).	*/
#define set_prev_size(p, sz) ((p)->mchunk_prev_size = (sz))

/* Ptr to previous physical malloc_chunk.	Only valid if !prev_inuse (P).	*/
#define prev_chunk(p) ((mchunkptr) (((char *) (p)) - prev_size (p)))

/* Treat space at ptr + offset as a chunk */
#define chunk_at_offset(p, s)	((mchunkptr) (((char *) (p)) + (s)))

/* extract p's inuse bit */
//通过查看虚拟地址相邻的下一个chunk的prev_inuse位来查看此chunk是否inuse
#define inuse(p)										\
	((((mchunkptr) (((char *) (p)) + chunksize (p)))->mchunk_size) & PREV_INUSE)

/* set/clear chunk as being inuse without otherwise disturbing */
#define set_inuse(p)										\
	((mchunkptr) (((char *) (p)) + chunksize (p)))->mchunk_size |= PREV_INUSE

#define clear_inuse(p)										\
	((mchunkptr) (((char *) (p)) + chunksize (p)))->mchunk_size &= ~(PREV_INUSE)


/* check/set/clear inuse bits in known places */
#define inuse_bit_at_offset(p, s)								\
	(((mchunkptr) (((char *) (p)) + (s)))->mchunk_size & PREV_INUSE)

#define set_inuse_bit_at_offset(p, s)								\
	(((mchunkptr) (((char *) (p)) + (s)))->mchunk_size |= PREV_INUSE)

#define clear_inuse_bit_at_offset(p, s)								\
	(((mchunkptr) (((char *) (p)) + (s)))->mchunk_size &= ~(PREV_INUSE))


/* Set size at head, without disturbing its use bit */
#define set_head_size(p, s)	((p)->mchunk_size = (((p)->mchunk_size & SIZE_BITS) | (s)))

/* Set size/use field */
#define set_head(p, s)			((p)->mchunk_size = (s))

/* Set size at footer (only when chunk is not in use) */
#define set_foot(p, s)			(((mchunkptr) ((char *) (p) + (s)))->mchunk_prev_size = (s))


#pragma GCC poison mchunk_size
#pragma GCC poison mchunk_prev_size

/*
	-------------------- Internal data structures --------------------

	All internal state is held in an instance of malloc_state defined
	below. There are no other static variables, except in two optional
	cases:
 * If USE_MALLOC_LOCK is defined, the mALLOC_MUTEx declared above.
 * If mmap doesn't support MAP_ANONYMOUS, a dummy file descriptor
		for mmap.

	Beware of lots of tricks that minimize the total bookkeeping space
	requirements. The result is a little over 1K bytes (for 4byte
	pointers and size_t.)
 */

/*
	Bins

		An array of bin headers for free chunks. Each bin is doubly
		linked.	The bins are approximately proportionally (log) spaced.
		There are a lot of these bins (128). This may look excessive, but
		works very well in practice.	Most bins hold sizes that are
		unusual as malloc request sizes, but are more usual for fragments
		and consolidated sets of chunks, which is what these bins hold, so
		they can be found quickly.	All procedures maintain the invariant
		that no consolidated chunk physically borders another one, so each
		chunk in a list is known to be preceeded and followed by either
		inuse chunks or the ends of memory.

		Chunks in bins are kept in size order, with ties going to the
		approximately least recently used chunk. Ordering isn't needed
		for the small bins, which all contain the same-sized chunks, but
		facilitates best-fit allocation for larger chunks. These lists
		are just sequential. Keeping them in order almost never requires
		enough traversal to warrant using fancier ordered data
		structures.

		Chunks of the same size are linked with the most
		recently freed at the front, and allocations are taken from the
		back.	This results in LRU (FIFO) allocation order, which tends
		to give each chunk an equal opportunity to be consolidated with
		adjacent freed chunks, resulting in larger free chunks and less
		fragmentation.

		To simplify use in double-linked lists, each bin header acts
		as a malloc_chunk. This avoids special-casing for headers.
		But to conserve space and improve locality, we allocate
		only the fd/bk pointers of bins, and then use repositioning tricks
		to treat these as the fields of a malloc_chunk*.
 */

typedef struct malloc_chunk *mbinptr;

/* addressing -- note that bin_at(0) does not exist */
#define bin_at(m, i) \
	(mbinptr) (((char *) &((m)->bins[((i) - 1) * 2]))						\
						- offsetof (struct malloc_chunk, fd))		//bins数组的特殊结构，返回对应bin的链表头chunk(伪chunk)

/* analog of ++bin */
#define next_bin(b)	((mbinptr) ((char *) (b) + (sizeof (mchunkptr) << 1)))

/* Reminders about list directionality within bins */
#define first(b)		((b)->fd)
#define last(b)			((b)->bk)


/*
!unlink过程中的检测
!1.后一个chunk的prev_size字段和此chunk的size字段是否相对应
!2.所在bin的双向链表中此chunk前后chunk的bk和fd指针是否指向本chunk
!3.若此chunk为large chunk，则其前后size指针应相对应
*/
#define unlink(AV, P, BK, FD) {												\
	if (__builtin_expect (chunksize(P) != prev_size (next_chunk(P)), 0))	\
		malloc_printerr ("corrupted size vs. prev_size");					\
	FD = P->fd;																\
	BK = P->bk;																\
	if (__builtin_expect (FD->bk != P || BK->fd != P, 0))					\
		malloc_printerr ("corrupted double-linked list");					\
	else																	\
	{																		\
		FD->bk = BK;														\
		BK->fd = FD;														\
		if (!in_smallbin_range (chunksize_nomask (P))						\
				&& __builtin_expect (P->fd_nextsize != NULL, 0)){			\
			if (__builtin_expect (P->fd_nextsize->bk_nextsize != P, 0)		\
					|| __builtin_expect (P->bk_nextsize->fd_nextsize != P, 0))	\
				malloc_printerr ("corrupted double-linked list (not small)");	\
			/*若相同大小的chunks不止P一个，则将P->fd作为新的相同大小的chunks中的第一个*/ \
			if (FD->fd_nextsize == NULL) {									\
				/*large bin中仅有一个size的chunks，P为这些chunks中的第一个*/	 \
				if (P->fd_nextsize == P)									\
					FD->fd_nextsize = FD->bk_nextsize = FD;					\
				/*large bin中不止一个size的chunks，P为与之相同大小chunks中的第一个*/\
				/*但P被unlink出这个large bin，此时P的fd指针指向的chunk则变为了相同大小chunks中的第一个chunk，需要使用size指针*/\
				else {														\
					FD->fd_nextsize = P->fd_nextsize;						\
					FD->bk_nextsize = P->bk_nextsize;						\
					P->fd_nextsize->bk_nextsize = FD;						\
					P->bk_nextsize->fd_nextsize = FD;						\
				}															\
			} 																\
			/*若相同大小的chunk只有P一个，则需要将其从size链表中unlink出来*/	    \
			else {															\
				P->fd_nextsize->bk_nextsize = P->bk_nextsize;				\
				P->bk_nextsize->fd_nextsize = P->fd_nextsize;				\
			}																\
		}																	\
	}																		\
}

/*
	Indexing

		Bins for sizes < 512 bytes contain chunks of all the same size, spaced
		8 bytes apart. Larger bins are approximately logarithmically spaced:

		64 bins of size			8
		32 bins of size			64
		16 bins of size		512
		8 bins of size		4096
		4 bins of size	32768
		2 bins of size	262144
		1 bin	of size what's left

		There is actually a little bit of slop in the numbers in bin_index
		for the sake of speed. This makes no difference elsewhere.

		The bins top out around 1MB because we expect to service large
		requests via mmap.

		Bin 0 does not exist.	Bin 1 is the unordered list; if that would be
		a valid chunk size the small bins are bumped up one.
 */

#define NBINS						128
#define NSMALLBINS				64
#define SMALLBIN_WIDTH		MALLOC_ALIGNMENT
#define SMALLBIN_CORRECTION (MALLOC_ALIGNMENT > 2 * SIZE_SZ)
#define MIN_LARGE_SIZE		((NSMALLBINS - SMALLBIN_CORRECTION) * SMALLBIN_WIDTH)

#define in_smallbin_range(sz)	\
	((unsigned long) (sz) < (unsigned long) MIN_LARGE_SIZE)

#define smallbin_index(sz) \
	((SMALLBIN_WIDTH == 16 ? (((unsigned) (sz)) >> 4) : (((unsigned) (sz)) >> 3))\
	+ SMALLBIN_CORRECTION)

#define largebin_index_32(sz)																								\
	(((((unsigned long) (sz)) >> 6) <= 38) ?	56 + (((unsigned long) (sz)) >> 6) :\
	((((unsigned long) (sz)) >> 9) <= 20) ?	91 + (((unsigned long) (sz)) >> 9) :\
	((((unsigned long) (sz)) >> 49) <= 10) ? 110 + (((unsigned long) (sz)) >> 12) :\
	((((unsigned long) (sz)) >> 15) <= 4) ? 119 + (((unsigned long) (sz)) >> 15) :\
	((((unsigned long) (sz)) >> 18) <= 2) ? 124 + (((unsigned long) (sz)) >> 18) :\
	126)

#define largebin_index_32_big(sz)																						\
	(((((unsigned long) (sz)) >> 6) <= 45) ?	49 + (((unsigned long) (sz)) >> 6) :\
	((((unsigned long) (sz)) >> 9) <= 20) ?	91 + (((unsigned long) (sz)) >> 9) :\
	((((unsigned long) (sz)) >> 12) <= 10) ? 110 + (((unsigned long) (sz)) >> 12) :\
	((((unsigned long) (sz)) >> 15) <= 4) ? 119 + (((unsigned long) (sz)) >> 15) :\
	((((unsigned long) (sz)) >> 18) <= 2) ? 124 + (((unsigned long) (sz)) >> 18) :\
	126)

// XXX It remains to be seen whether it is good to keep the widths of
// XXX the buckets the same or whether it should be scaled by a factor
// XXX of two as well.
#define largebin_index_64(sz)																								\
	(((((unsigned long) (sz)) >> 6) <= 48) ?	48 + (((unsigned long) (sz)) >> 6) :\
	((((unsigned long) (sz)) >> 9) <= 20) ?	91 + (((unsigned long) (sz)) >> 9) :\
	((((unsigned long) (sz)) >> 12) <= 10) ? 110 + (((unsigned long) (sz)) >> 12) :\
	((((unsigned long) (sz)) >> 15) <= 4) ? 119 + (((unsigned long) (sz)) >> 15) :\
	((((unsigned long) (sz)) >> 18) <= 2) ? 124 + (((unsigned long) (sz)) >> 18) :\
	126)

#define largebin_index(sz) \
	(SIZE_SZ == 8 ? largebin_index_64 (sz)																		\
	: MALLOC_ALIGNMENT == 16 ? largebin_index_32_big (sz)										\
	: largebin_index_32 (sz))

#define bin_index(sz) \
	((in_smallbin_range (sz)) ? smallbin_index (sz) : largebin_index (sz))


/*
	Unsorted chunks

		All remainders from chunk splits, as well as all returned chunks,
		are first placed in the "unsorted" bin. They are then placed
		in regular bins after malloc gives them ONE chance to be used before
		binning. So, basically, the unsorted_chunks list acts as a queue,
		with chunks being placed on it in free (and malloc_consolidate),
		and taken off (to be either used or placed in bins) in malloc.

		The NON_MAIN_ARENA flag is never set for unsorted chunks, so it
		does not have to be taken into account in size comparisons.
 */

/* The otherwise unindexable 1-bin is used to hold unsorted chunks. */
//获取指向unsorted bin表头(伪)chunk的指针
#define unsorted_chunks(M)					(bin_at (M, 1))

/*
	Top

		The top-most available chunk (i.e., the one bordering the end of
		available memory) is treated specially. It is never included in
		any bin, is used only if no other chunk is available, and is
		released back to the system if it is very large (see
		M_TRIM_THRESHOLD).	Because top initially
		points to its own bin with initial zero size, thus forcing
		extension on the first malloc request, we avoid having any special
		code in malloc to check whether it even exists yet. But we still
		need to do so when getting memory from system, so we make
		initial_top treat the bin as a legal but unusable chunk during the
		interval between initialization and the first call to
		sysmalloc. (This is somewhat delicate, since it relies on
		the 2 preceding words to be zero during this interval as well.)
 */

/* Conveniently, the unsorted bin can be used as dummy top on first call */
#define initial_top(M)							(unsorted_chunks (M))

/*
	Binmap

		To help compensate for the large number of bins, a one-level index
		structure is used for bin-by-bin searching.	`binmap' is a
		bitvector recording whether bins are definitely empty so they can
		be skipped over during during traversals.	The bits are NOT always
		cleared as soon as bins are empty, but instead only
		when they are noticed to be empty during traversal in malloc.
 */

/* Conservatively use 32 bits per map word, even if on 64bit system */
#define BINMAPSHIFT			5
#define BITSPERMAP			(1U << BINMAPSHIFT)
#define BINMAPSIZE			(NBINS / BITSPERMAP)

#define idx2block(i)		((i) >> BINMAPSHIFT)
#define idx2bit(i)			((1U << ((i) & ((1U << BINMAPSHIFT) - 1))))

#define mark_bin(m, i)		((m)->binmap[idx2block (i)] |= idx2bit (i))
#define unmark_bin(m, i)	((m)->binmap[idx2block (i)] &= ~(idx2bit (i)))
#define get_binmap(m, i)	((m)->binmap[idx2block (i)] & idx2bit (i))

/*
	Fastbins

		An array of lists holding recently freed small chunks.	Fastbins
		are not doubly linked.	It is faster to single-link them, and
		since chunks are never removed from the middles of these lists,
		double linking is not necessary. Also, unlike regular bins, they
		are not even processed in FIFO order (they use faster LIFO) since
		ordering doesn't much matter in the transient contexts in which
		fastbins are normally used.

		Chunks in fastbins keep their inuse bit set, so they cannot
		be consolidated with other free chunks. malloc_consolidate
		releases all chunks in fastbins and consolidates them with
		other free chunks.
 */

typedef struct malloc_chunk *mfastbinptr;

//访问当前arena的malloc_state结构体中的fastbinsY指针数组，访问相应index
#define fastbin(ar_ptr, idx) ((ar_ptr)->fastbinsY[idx])		

/* offset 2 to use otherwise unindexable first 2 bins */
#define fastbin_index(sz) \
	((((unsigned int) (sz)) >> (SIZE_SZ == 8 ? 4 : 3)) - 2)


/* The maximum fastbin request size we support */
//64bit下最大fastbin大小为160bit(请求size)
#define MAX_FAST_SIZE		(80 * SIZE_SZ / 4)		

//FASTBINS的个数和最大FASTBIN SIZE相符，为10个，默认情况下使用8个 
#define NFASTBINS	(fastbin_index (request2size (MAX_FAST_SIZE)) + 1)	

/*
	FASTBIN_CONSOLIDATION_THRESHOLD is the size of a chunk in free()
	that triggers automatic consolidation of possibly-surrounding
	fastbin chunks. This is a heuristic, so the exact value should not
	matter too much. It is defined at half the default trim threshold as a
	compromise heuristic to only attempt consolidation if it is likely
	to lead to trimming. However, it is not dynamically tunable, since
	consolidation reduces fragmentation surrounding large chunks even
	if trimming is not used.
 */

#define FASTBIN_CONSOLIDATION_THRESHOLD	(65536UL)

/*
	NONCONTIGUOUS_BIT indicates that MORECORE does not return contiguous
	regions.	Otherwise, contiguity is exploited in merging together,
	when possible, results from consecutive MORECORE calls.

	The initial value comes from MORECORE_CONTIGUOUS, but is
	changed dynamically if mmap is ever used as an sbrk substitute.
 */
//morecore无法返回连续的空间
#define NONCONTIGUOUS_BIT		(2U)

#define contiguous(M)					(((M)->flags & NONCONTIGUOUS_BIT) == 0)
#define noncontiguous(M)			(((M)->flags & NONCONTIGUOUS_BIT) != 0)
#define set_noncontiguous(M)	((M)->flags |= NONCONTIGUOUS_BIT)
#define set_contiguous(M)			((M)->flags &= ~NONCONTIGUOUS_BIT)

/* Maximum size of memory handled in fastbins.	*/
static INTERNAL_SIZE_T global_max_fast;

/*
	Set value of max_fast.
	Use impossibly small value if 0.
	Precondition: there are no existing fastbin chunks in the main arena.
	Since do_check_malloc_state () checks this, we call malloc_consolidate ()
	before changing max_fast.	Note other arenas will leak their fast bin
	entries if max_fast is reduced.
 */

#define set_max_fast(s) \
	global_max_fast = (((s) == 0)									\
										? SMALLBIN_WIDTH : ((s + SIZE_SZ) & ~MALLOC_ALIGN_MASK))

static inline INTERNAL_SIZE_T
get_max_fast (void)
{
	/* Tell the GCC optimizers that global_max_fast is never larger
		than MAX_FAST_SIZE.	This avoids out-of-bounds array accesses in
		_int_malloc after constant propagation of the size parameter.
		(The code never executes because malloc preserves the
		global_max_fast invariant, but the optimizers may not recognize
		this.)	*/
	if (global_max_fast > MAX_FAST_SIZE)
		__builtin_unreachable ();
	return global_max_fast;
}

/*
	----------- Internal state representation and initialization -----------
 */

/*
	have_fastchunks indicates that there are probably some fastbin chunks.
	It is set true on entering a chunk into any fastbin, and cleared early in
	malloc_consolidate.	The value is approximate since it may be set when there
	are no fastbin chunks, or it may be clear even if there are fastbin chunks
	available.	Given it's sole purpose is to reduce number of redundant calls to
	malloc_consolidate, it does not affect correctness.	As a result we can safely
	use relaxed atomic accesses.
 */


struct malloc_state
{
	/* Serialize access.	*/
	__libc_lock_define (, mutex);

	/* Flags (formerly in max_fast).	*/
	int flags;

	/* Set if the fastbin chunks contain recently inserted free blocks.	*/
	/* Note this is a bool but not all targets support atomics on booleans.	*/
	int have_fastchunks;

	/* Fastbins */
	mfastbinptr fastbinsY[NFASTBINS];

	/* Base of the topmost chunk -- not otherwise kept in a bin */
	mchunkptr top;

	/* The remainder from the most recent split of a small request */
	mchunkptr last_remainder;

	/* Normal bins packed as described above */
	/*
	bins链表头数组
	small bins和large bins中的每个bin在bins数组中均占据两个index
	第一个位置为fd指针，第二个为bk指针
	获取链表头时，将对应bin位置地址 - offsetof(struct malloc_chunk, fd),从而获得本应为chunk头的地方，便于当作chunk统一处理
	提升了cpu cache命中率，增加效率
	*/
	mchunkptr bins[NBINS * 2 - 2];

	/* Bitmap of bins */
	//无论是32bit/64bit，均使用int(32bit)进行bitmap存储
	//每个bin对应一个bit，从index1(unsorted bin)开始
	//若bin中存在chunk，正在使用则设置为1,否则为0
	unsigned int binmap[BINMAPSIZE];

	/* Linked list */
	struct malloc_state *next;

	/* Linked list for free arenas.	Access to this field is serialized
		by free_list_lock in arena.c.	*/
	struct malloc_state *next_free;

	/* Number of threads attached to this arena.	0 if the arena is on
		the free list.	Access to this field is serialized by
		free_list_lock in arena.c.	*/
	INTERNAL_SIZE_T attached_threads;

	/* Memory allocated from the system in this arena.	*/
	INTERNAL_SIZE_T system_mem;
	INTERNAL_SIZE_T max_system_mem;
};

struct malloc_par
{
	/* Tunable parameters */
	unsigned long trim_threshold;
	INTERNAL_SIZE_T top_pad;
	INTERNAL_SIZE_T mmap_threshold;
	//以下两个字段标志ptmalloc管理的最多arena数量
	//若arena_max被设置，则arena_test字段无效
	INTERNAL_SIZE_T arena_test;
	INTERNAL_SIZE_T arena_max;

	/* Memory map support */
	int n_mmaps;
	int n_mmaps_max;
	int max_n_mmaps;
	/* the mmap_threshold is dynamic, until the user sets
		it manually, at which point we need to disable any
		dynamic behavior. */
	int no_dyn_threshold;

	/* Statistics */
	INTERNAL_SIZE_T mmapped_mem;
	INTERNAL_SIZE_T max_mmapped_mem;

	/* First address handed out by MORECORE/sbrk.	*/
	char *sbrk_base;

#if USE_TCACHE
	/* Maximum number of buckets to use.	*/
	size_t tcache_bins;
	size_t tcache_max_bytes;
	/* Maximum number of chunks in each bucket.	*/
	size_t tcache_count;
	/* Maximum number of chunks to remove from the unsorted list, which
		aren't used to prefill the cache.	*/
	size_t tcache_unsorted_limit;
#endif
};

/* There are several instances of this struct ("arenas") in this
	malloc.	If you are adapting this malloc in a way that does NOT use
	a static or mmapped malloc_state, you MUST explicitly zero-fill it
	before using. This malloc relies on the property that malloc_state
	is initialized to all zeroes (as is true of C statics).	*/

static struct malloc_state main_arena = 
{
	.mutex = _LIBC_LOCK_INITIALIZER,
	.next = &main_arena,
	.attached_threads = 1
};

/* These variables are used for undumping support.	Chunked are marked
	as using mmap, but we leave them alone if they fall into this
	range.	NB: The chunk size for these chunks only includes the
	initial size field (of SIZE_SZ bytes), there is no trailing size
	field (unlike with regular mmapped chunks).	*/
static mchunkptr dumped_main_arena_start; /* Inclusive.	*/
static mchunkptr dumped_main_arena_end;	/* Exclusive.	*/

/* True if the pointer falls into the dumped arena.	Use this after
	chunk_is_mmapped indicates a chunk is mmapped.	*/
#define DUMPED_MAIN_ARENA_CHUNK(p) \
	((p) >= dumped_main_arena_start && (p) < dumped_main_arena_end)

/* There is only one instance of the malloc parameters.	*/

static struct malloc_par mp_ =
{
	.top_pad = DEFAULT_TOP_PAD,
	.n_mmaps_max = DEFAULT_MMAP_MAX,
	.mmap_threshold = DEFAULT_MMAP_THRESHOLD,
	.trim_threshold = DEFAULT_TRIM_THRESHOLD,
#define NARENAS_FROM_NCORES(n) ((n) * (sizeof (long) == 4 ? 2 : 8))
	.arena_test = NARENAS_FROM_NCORES (1)
#if USE_TCACHE
	,
	.tcache_count = TCACHE_FILL_COUNT,
	.tcache_bins = TCACHE_MAX_BINS,
	.tcache_max_bytes = tidx2usize (TCACHE_MAX_BINS-1),
	.tcache_unsorted_limit = 0 /* No limit.	*/
#endif
};

/*
	Initialize a malloc_state struct.

	This is called from ptmalloc_init () or from _int_new_arena ()
	when creating a new arena.
 */
//初始化malloc_state结构体
static void
malloc_init_state (mstate av)
{
	int i;
	mbinptr bin;

	//初始化所有由bins数组管理的bins的双向循环链表
	for (i = 1; i < NBINS; ++i)
	{
		bin = bin_at (av, i);
		bin->fd = bin->bk = bin;
	}
//除sbrk空间连续，且当前arena为main arena的情况外，其余情况均设置不连续位
#if MORECORE_CONTIGUOUS
	if (av != &main_arena)
#endif
		set_noncontiguous (av);
	//若为main arena，则设置global_max_fast
	//若不为main arena，则说明global_max_fast已初始化，不需要再次设置
	if (av == &main_arena)
		set_max_fast (DEFAULT_MXFAST);
	//设置当前arena无fastbin chunk
	atomic_store_relaxed (&av->have_fastchunks, false);
	av->top = initial_top (av);
}

/*
	Other internal utilities operating on mstates
 */

static void *sysmalloc (INTERNAL_SIZE_T, mstate);
static int			systrim (size_t, mstate);
static void		malloc_consolidate (mstate);


/* -------------- Early definitions for debugging hooks ---------------- */

/* Define and initialize the hook variables.	These weak definitions must
	appear before any use of the variables in a function (arena.c uses one).	*/
#ifndef weak_variable
/* In GNU libc we want the hook variables to be weak definitions to
	avoid a problem with Emacs.	*/
# define weak_variable weak_function
#endif

/* Forward declarations.	*/
static void *malloc_hook_ini (size_t sz,
															const void *caller) __THROW;
static void *realloc_hook_ini (void *ptr, size_t sz,
															const void *caller) __THROW;
static void *memalign_hook_ini (size_t alignment, size_t sz,
																const void *caller) __THROW;

#if HAVE_MALLOC_INIT_HOOK
void weak_variable (*__malloc_initialize_hook) (void) = NULL;
compat_symbol (libc, __malloc_initialize_hook,
				__malloc_initialize_hook, GLIBC_2_0);
#endif

void weak_variable (*__free_hook) (void *__ptr,
																	const void *) = NULL;
void *weak_variable (*__malloc_hook)
	(size_t __size, const void *) = malloc_hook_ini;
void *weak_variable (*__realloc_hook)
	(void *__ptr, size_t __size, const void *)
	= realloc_hook_ini;
void *weak_variable (*__memalign_hook)
	(size_t __alignment, size_t __size, const void *)
	= memalign_hook_ini;
void weak_variable (*__after_morecore_hook) (void) = NULL;

/* This function is called from the arena shutdown hook, to free the
	thread cache (if it exists).	*/
static void tcache_thread_shutdown (void);

/* ------------------ Testing support ----------------------------------*/

static int perturb_byte;

static void
alloc_perturb (char *p, size_t n)
{
	if (__glibc_unlikely (perturb_byte))
		memset (p, perturb_byte ^ 0xff, n);
}

static void
free_perturb (char *p, size_t n)
{
	if (__glibc_unlikely (perturb_byte))
		memset (p, perturb_byte, n);
}



#include <stap-probe.h>

/* ------------------- Support for multiple arenas -------------------- */
#include "arena.c"

/*
	Debugging support

	These routines make a number of assertions about the states
	of data structures that should be true at all times. If any
	are not true, it's very likely that a user program has somehow
	trashed memory. (It's also possible that there is a coding error
	in malloc. In which case, please report it!)
 */

#if !MALLOC_DEBUG

# define check_chunk(A, P)
# define check_free_chunk(A, P)
# define check_inuse_chunk(A, P)
# define check_remalloced_chunk(A, P, N)
# define check_malloced_chunk(A, P, N)
# define check_malloc_state(A)

#else

# define check_chunk(A, P)							do_check_chunk (A, P)
# define check_free_chunk(A, P)				do_check_free_chunk (A, P)
# define check_inuse_chunk(A, P)				do_check_inuse_chunk (A, P)
# define check_remalloced_chunk(A, P, N) do_check_remalloced_chunk (A, P, N)
# define check_malloced_chunk(A, P, N)	do_check_malloced_chunk (A, P, N)
# define check_malloc_state(A)				do_check_malloc_state (A)

//检查所有chunk必须满足的属性
/*
1.非mmapped chunk位置必须位于该arena的分配区域中，mmapped chunk位置必须位于该arena之外
2.对top chunk有特殊检测：大小必须大于MIN_SIZE，prev_inuse位必须为1
*/
static void
do_check_chunk (mstate av, mchunkptr p)
{
	unsigned long sz = chunksize (p);
	//最大&最小heap地址
	char *max_address = (char *) (av->top) + chunksize (av->top);
	char *min_address = max_address - av->system_mem;

	//chunk非mmaped
	if (!chunk_is_mmapped (p))
		{
			//chunk非top chunk
			if (p != av->top)
				{
					if (contiguous (av))
						{
							//检测chunk的位置是否合法
							assert (((char *) p) >= min_address);
							assert (((char *) p + sz) <= ((char *) (av->top)));
						}
				}
			//是top chunk
			else
				{
					//检测top chunk大小与属性是否合法
					/* top size is always at least MINSIZE */
					assert ((unsigned long) (sz) >= MINSIZE);
					/* top predecessor always marked inuse */
					assert (prev_inuse (p));
				}
		}
	//为mmaped chunk，且chunk地址位于main heap之外
	else if (!DUMPED_MAIN_ARENA_CHUNK (p))
		{
			if (contiguous (av) && av->top != initial_top (av))
				{
					assert (((char *) p) < min_address || ((char *) p) >= max_address);
				}
			/* chunk is page-aligned */
			assert (((prev_size (p) + sz) & (GLRO (dl_pagesize) - 1)) == 0);
			/* mem is aligned */
			assert (aligned_OK (chunk2mem (p)));
		}
}

/*
	Properties of free chunks
 */

static void
do_check_free_chunk (mstate av, mchunkptr p)
{
	INTERNAL_SIZE_T sz = chunksize_nomask (p) & ~(PREV_INUSE | NON_MAIN_ARENA);
	mchunkptr next = chunk_at_offset (p, sz);

	do_check_chunk (av, p);

	//下一个chunk的prev_inuse位必须为0，且非mmapped
	assert (!inuse (p));
	assert (!chunk_is_mmapped (p));

	/* Unless a special marker, must have OK fields */
	if ((unsigned long) (sz) >= MINSIZE)
		{
			//!检测对齐情况
			assert ((sz & MALLOC_ALIGN_MASK) == 0);
			assert (aligned_OK (chunk2mem (p)));
			//!检测size&prev_size域
			assert (prev_size (next_chunk (p)) == sz);
			//!检测前后chunk是否在使用之中，若没有，则本应该合并而未合并，故报错
			assert (prev_inuse (p));
			assert (next == av->top || inuse (next));
			//!检测双向链表指针是否存在问题
			assert (p->fd->bk == p);
			assert (p->bk->fd == p);
		}
	else /* markers are always of size SIZE_SZ */
		assert (sz == SIZE_SZ);
}

/*
	Properties of inuse chunks
 */

static void
do_check_inuse_chunk (mstate av, mchunkptr p)
{
	mchunkptr next;
//本chunk检测
	//!检测chunk地址是否位于heap区域之内，位置是否合法
	do_check_chunk (av, p);
	//若chunk 为 mmapped，则检测完成(没有prev chunk)
	if (chunk_is_mmapped (p))
		return; 
	//!检测inuse位，若非inuse则报错
	assert (inuse (p));


	next = next_chunk (p);
//前侧chunk检测
	//!若前一个chunk非inuse，检查此chunk的prev_size和上一个chunk的size字段是否匹配
	if (!prev_inuse (p))
		{
			/* Note that we cannot even look at prev unless it is not inuse */
			mchunkptr prv = prev_chunk (p);
			assert (next_chunk (prv) == p);
			//!检测前一个chunk是否符合free chunk的特性
			do_check_free_chunk (av, prv);
		}
//后侧chunk检测
	//!若下一个chunk为top chunk，则检测其大小和prev_inuse位(恒为1)
	if (next == av->top)
		{
			assert (prev_inuse (next));
			assert (chunksize (next) >= MINSIZE);
		}
	//!若下一个chunk为free状态，则检测是否符合特征
	else if (!inuse (next))
		do_check_free_chunk (av, next);
}

/*
	Properties of chunks recycled from fastbins
 */

static void
do_check_remalloced_chunk (mstate av, mchunkptr p, INTERNAL_SIZE_T s)
{
	INTERNAL_SIZE_T sz = chunksize_nomask (p) & ~(PREV_INUSE | NON_MAIN_ARENA);

	if (!chunk_is_mmapped (p))
		{
			assert (av == arena_for_chunk (p));
			if (chunk_main_arena (p))
				assert (av == &main_arena);
			else
				assert (av != &main_arena);
		}

	do_check_inuse_chunk (av, p);

	/* Legal size ... */
	assert ((sz & MALLOC_ALIGN_MASK) == 0);
	assert ((unsigned long) (sz) >= MINSIZE);
	/* ... and alignment */
	assert (aligned_OK (chunk2mem (p)));
	/* chunk is less than MINSIZE more than request */
	assert ((long) (sz) - (long) (s) >= 0);
	assert ((long) (sz) - (long) (s + MINSIZE) < 0);
}

/*
	Properties of nonrecycled chunks at the point they are malloced
 */

static void
do_check_malloced_chunk (mstate av, mchunkptr p, INTERNAL_SIZE_T s)
{
	/* same as recycled case ... */
	do_check_remalloced_chunk (av, p, s);

	/*
		... plus,	must obey implementation invariant that prev_inuse is
		always true of any allocated chunk; i.e., that each allocated
		chunk borders either a previously allocated and still in-use
		chunk, or the base of its memory arena. This is ensured
		by making all allocations from the `lowest' part of any found
		chunk.	This does not necessarily hold however for chunks
		recycled via fastbins.
	*/

	assert (prev_inuse (p));
}


/*
	Properties of malloc_state.

	This may be useful for debugging malloc, as well as detecting user
	programmer errors that somehow write into malloc_state.

	If you are extending or experimenting with this malloc, you can
	probably figure out how to hack this routine to print out or
	display chunk addresses, sizes, bins, and other instrumentation.
 */

static void
do_check_malloc_state (mstate av)
{
	int i;
	mchunkptr p;
	mchunkptr q;
	mbinptr b;
	unsigned int idx;
	INTERNAL_SIZE_T size;
	unsigned long total = 0;
	int max_fast_bin;

	/* internal size_t must be no wider than pointer type */
	assert (sizeof (INTERNAL_SIZE_T) <= sizeof (char *));

	/* alignment is a power of 2 */
	assert ((MALLOC_ALIGNMENT & (MALLOC_ALIGNMENT - 1)) == 0);

	/* Check the arena is initialized. */
	assert (av->top != 0);

	/* No memory has been allocated yet, so doing more tests is not possible.	*/
	if (av->top == initial_top (av))
		return;

	/* pagesize is a power of 2 */
	assert (powerof2(GLRO (dl_pagesize)));

	/* A contiguous main_arena is consistent with sbrk_base.	*/
	if (av == &main_arena && contiguous (av))
		assert ((char *) mp_.sbrk_base + av->system_mem ==
						(char *) av->top + chunksize (av->top));

	/* properties of fastbins */

	/* max_fast is in allowed range */
	assert ((get_max_fast () & ~1) <= request2size (MAX_FAST_SIZE));

	max_fast_bin = fastbin_index (get_max_fast ());

	for (i = 0; i < NFASTBINS; ++i)
		{
			p = fastbin (av, i);

			/* The following test can only be performed for the main arena.
				While mallopt calls malloc_consolidate to get rid of all fast
				bins (especially those larger than the new maximum) this does
				only happen for the main arena.	Trying to do this for any
				other arena would mean those arenas have to be locked and
				malloc_consolidate be called for them.	This is excessive.	And
				even if this is acceptable to somebody it still cannot solve
				the problem completely since if the arena is locked a
				concurrent malloc call might create a new arena which then
				could use the newly invalid fast bins.	*/

			/* all bins past max_fast are empty */
			if (av == &main_arena && i > max_fast_bin)
				assert (p == 0);

			while (p != 0)
				{
					/* each chunk claims to be inuse */
					do_check_inuse_chunk (av, p);
					total += chunksize (p);
					/* chunk belongs in this bin */
					assert (fastbin_index (chunksize (p)) == i);
					p = p->fd;
				}
		}

	/* check normal bins */
	for (i = 1; i < NBINS; ++i)
		{
			b = bin_at (av, i);

			/* binmap is accurate (except for bin 1 == unsorted_chunks) */
			if (i >= 2)
				{
					unsigned int binbit = get_binmap (av, i);
					int empty = last (b) == b;
					if (!binbit)
						assert (empty);
					else if (!empty)
						assert (binbit);
				}

			for (p = last (b); p != b; p = p->bk)
				{
					/* each chunk claims to be free */
					do_check_free_chunk (av, p);
					size = chunksize (p);
					total += size;
					if (i >= 2)
						{
							/* chunk belongs in bin */
							idx = bin_index (size);
							assert (idx == i);
							/* lists are sorted */
							assert (p->bk == b ||
											(unsigned long) chunksize (p->bk) >= (unsigned long) chunksize (p));

							if (!in_smallbin_range (size))
								{
									if (p->fd_nextsize != NULL)
										{
											if (p->fd_nextsize == p)
												assert (p->bk_nextsize == p);
											else
												{
													if (p->fd_nextsize == first (b))
														assert (chunksize (p) < chunksize (p->fd_nextsize));
													else
														assert (chunksize (p) > chunksize (p->fd_nextsize));

													if (p == first (b))
														assert (chunksize (p) > chunksize (p->bk_nextsize));
													else
														assert (chunksize (p) < chunksize (p->bk_nextsize));
												}
										}
									else
										assert (p->bk_nextsize == NULL);
								}
						}
					else if (!in_smallbin_range (size))
						assert (p->fd_nextsize == NULL && p->bk_nextsize == NULL);
					/* chunk is followed by a legal chain of inuse chunks */
					for (q = next_chunk (p);
							(q != av->top && inuse (q) &&
								(unsigned long) (chunksize (q)) >= MINSIZE);
							q = next_chunk (q))
						do_check_inuse_chunk (av, q);
				}
		}

	/* top chunk is OK */
	check_chunk (av, av->top);
}
#endif


/* ----------------- Support for debugging hooks -------------------- */
#include "hooks.c"


/* ----------- Routines dealing with system allocation -------------- */

/*
	sysmalloc handles malloc cases requiring more memory from the system.
	On entry, it is assumed that av->top does not have enough
	space to service request for nb bytes, thus requiring that av->top
	be extended or replaced.
 */

static void *
sysmalloc (INTERNAL_SIZE_T nb, mstate av)
{
	mchunkptr old_top;							/* incoming value of av->top */
	INTERNAL_SIZE_T old_size;			/* its size */
	char *old_end;									/* its end address */

	long size;											/* arg to first MORECORE or mmap call */
	char *brk;											/* return value from MORECORE */

	long correction;								/* arg to 2nd MORECORE call */
	char *snd_brk;									/* 2nd return val */

	INTERNAL_SIZE_T front_misalign; /* unusable bytes at front of new space */
	INTERNAL_SIZE_T end_misalign;	/* partial page left at end of new space */
	char *aligned_brk;							/* aligned offset into brk */

	mchunkptr p;										/* the allocated/returned chunk */
	mchunkptr remainder;						/* remainder from allocation */
	unsigned long remainder_size;	/* its size */


	size_t pagesize = GLRO (dl_pagesize);
	bool tried_mmap = false;


	/*
		If have mmap, and the request size meets the mmap threshold, and
		the system supports mmap, and there are few enough currently
		allocated mmapped regions, try to directly map this request
		rather than expanding top.
	*/
	//若：1）1.需求size大小大于mmap分配阈值
	//      2.且malloc中的mmap分配chunk数还未超过限制
	//   2）或无Arena可用(全部使用中)
	//则使用mmap分配
	if (av == NULL
		|| ((unsigned long) (nb) >= (unsigned long) (mp_.mmap_threshold)
		&& (mp_.n_mmaps < mp_.n_mmaps_max)))
	{
		char *mm;					/* return value from mmap call*/

	try_mmap:
		/*
			Round up size to nearest page.	For mmapped chunks, the overhead
			is one SIZE_SZ unit larger than for normal chunks, because there
			is no following chunk whose prev_size field could be used.

			See the front_misalign handling below, for glibc there is no
			need for further alignments unless we have have high alignment.
		*/
		//将分配的chunk size向上对其到一个page的大小
		if (MALLOC_ALIGNMENT == 2 * SIZE_SZ)
			size = ALIGN_UP (nb + SIZE_SZ, pagesize);
		else
			size = ALIGN_UP (nb + SIZE_SZ + MALLOC_ALIGN_MASK, pagesize);
		tried_mmap = true;

		/* Don't try if size wraps around 0 */
		//检测size & 需求chunk size的大小关系，进入mmap流程
		if ((unsigned long) (size) > (unsigned long) (nb))
		{
			//默认给予读写权限，不可执行
			mm = (char *) (MMAP (0, size, PROT_READ | PROT_WRITE, 0));

			//mmap分配成功
			if (mm != MAP_FAILED)
			{
				/*
					The offset to the start of the mmapped region is stored
					in the prev_size field of the chunk. This allows us to adjust
					returned start address to meet alignment requirements here
					and in memalign(), and still be able to compute proper
					address argument for later munmap in free() and realloc().
				*/

				//此处检测mem指针是否对其需要对齐的地址
				if (MALLOC_ALIGNMENT == 2 * SIZE_SZ)
				{
					/* For glibc, chunk2mem increases the address by 2*SIZE_SZ and
						MALLOC_ALIGN_MASK is 2*SIZE_SZ-1.	Each mmap'ed area is page
						aligned and therefore definitely MALLOC_ALIGN_MASK-aligned.	*/
					assert (((INTERNAL_SIZE_T) chunk2mem (mm) & MALLOC_ALIGN_MASK) == 0);
					front_misalign = 0;
				}
				else
					front_misalign = (INTERNAL_SIZE_T) chunk2mem (mm) & MALLOC_ALIGN_MASK;
				//若未对齐，则计算修正值，将mem指针向后修正
				//随后在纠正后的chunk的prev_size中写入修正值(标明prev chunk未在使用中)，使此chunk在free时可与修正的部分合并
				//完美避免了空间碎片，同时也保证了chunk头部的对齐，便于寻址，提高效率
				if (front_misalign > 0)
				{
					correction = MALLOC_ALIGNMENT - front_misalign;
					p = (mchunkptr) (mm + correction);
					set_prev_size (p, correction);
					set_head (p, (size - correction) | IS_MMAPPED);
				}
				//已对齐，不需要调整，直接设置相关位即可
				//*注意，此处的prev_size位设为了0
				else
				{
					p = (mchunkptr) mm;
					set_prev_size (p, 0);
					set_head (p, size | IS_MMAPPED);
				}

				/* update statistics */
				//原子操作，对malloc管理结构体malloc_par中mmap chunk计数字段进行同步(+1)
				int new = atomic_exchange_and_add (&mp_.n_mmaps, 1) + 1;
				atomic_max (&mp_.max_n_mmaps, new);

				unsigned long sum;
				//原子操作，对malloc管理结构体malloc_par中mmap chunk总内存占有量字段进行同步
				sum = atomic_exchange_and_add (&mp_.mmapped_mem, size) + size;
				//同步同一时刻ptmalloc管理的最大mmap chunk内存占有量
				atomic_max (&mp_.max_mmapped_mem, sum);
				//检测chunk，转换并返回用户指针
				check_chunk (av, p);
				return chunk2mem (p);
			}
		}
	}

	/* There are no usable arenas and mmap also failed.	*/
	//无arena可用，且mmap分配失败，则整个malloc流程失败
	if (av == NULL)
		return 0;

	/* Record incoming configuration of top */
	//*到达此处所有分配请求都已获取到arena
	//*若请求大于mmap分配阈值则说明mmap失败或者mmap chunk数量达到极限
	old_top = av->top;
	//找到当前arena的top chunk的最高地址处
	old_size = chunksize (old_top);
	old_end = (char *) (chunk_at_offset (old_top, old_size));
<<<<<<< HEAD
	//brk相关指针设置为0
=======
	//获取当前brk区域尾部指针
>>>>>>> ddf090c16f88a886f70e51b6cab3165f8cfdf44c
	brk = snd_brk = (char *) (MORECORE_FAILURE);

	/*
		If not the first time through, we require old_size to be
		at least MINSIZE and to have prev_inuse set.
	*/
	//initial_top (av)即unsorted_chunks(av)为bins[0]-2*SIZE_SZ，正好指向malloc_state结构体中top指针
	//检测top chunk是否满足下列两种情况中的一种
	//1).1.top chunk size为0
	//   2.malloc_state结构体未被更改(通过av->top获取的top chunk和通过bins数组+offset获取的top chunk指针一致)
	//2).1.top chunk size大于chunk的最小size
	//   2.且top chunk的prev_inuse位已置位
	//   3.且top chunk的尾部与页对其
	assert ((old_top == initial_top (av) && old_size == 0) ||
				((unsigned long) (old_size) >= MINSIZE &&
					prev_inuse (old_top) &&
					((unsigned long) old_end & (pagesize - 1)) == 0));

	/* Precondition: not enough current space to satisfy nb request */
	//检测是否top chunk确实没有足够的空间进行需求chunk的分配
	assert ((unsigned long) (old_size) < (unsigned long) (nb + MINSIZE));

	//*此处为:
	//*1.各个检测通过
	//*2.有分配到arena但不是main arena
	//*3.mmap流程失败或需分配的chunk size未超过mmap分配阈值或mmap chunk数量超过限制
	if (av != &main_arena)
	{
		heap_info *old_heap, *heap;
		size_t old_heap_size;

		/* First try to extend the current heap. */
		//通过top chunk的指针推出当前heap的头部指针
		//top chunk位于heap中，heap最大内存占用量为HEAP_MAX_SIZE
		//heap的开头地址对齐HEAP_MAX_SIZE宽度
		//通过top_chunk_ptr & ~(HEAP_MAX_SIZE - 1)得到heap开头
		old_heap = heap_for_ptr (old_top);
		//heap开头处为heap_info结构体，其中size字段存储了heap的总大小
		old_heap_size = old_heap->size;
		//*增加当前heap的大小
		//若需求chunk size大于现有的top chunk，并且heap size增长成功,则使用增长部分的空间
		if ((long) (MINSIZE + nb - old_size) > 0
			&& grow_heap (old_heap, MINSIZE + nb - old_size) == 0)
		{
			//调整整个arena的内存占用量
			av->system_mem += old_heap->size - old_heap_size;
			//将top chunk的size字段增加上heap增长的部分
			set_head (old_top, (((char *) old_heap + old_heap->size) - (char *) old_top)
								| PREV_INUSE);
		}
		//*创建新的heap
		//*若当前heap增长失败(单个heap size超出限制)，则创建一个新的heap
		// 其大小为需求chunk的大小加heap_info结构体的大小再加默认top chunk大小
		else if ((heap = new_heap (nb + (MINSIZE + sizeof (*heap)), mp_.top_pad)))
		{
			/* Use a newly allocated heap.	*/
			//标记创建的新heap属于此arena，将新的heap的prev heap指针中填上原本的heap(heap单向链表)
			//更新arena管理结构体malloc_state的内存占用量字段
			heap->ar_ptr = av;
			heap->prev = old_heap;
			av->system_mem += heap->size;
			/* Set up the new top.	*/
			//设置新heap在heap管理结构体heap_info后的空间均为top chunk
			//将此arena的top chunk指针指向新的top chunk上
			//设置top chunk相应位(保证top chunk的prev_inuse位恒为1)
			top (av) = chunk_at_offset (heap, sizeof (*heap));
			set_head (top (av), (heap->size - sizeof (*heap)) | PREV_INUSE);

			/* Setup fencepost and free the old top chunk with a multiple of
				MALLOC_ALIGNMENT in size. */
			/* The fencepost takes at least MINSIZE bytes, because it might
				become the top chunk again later.	Note that a footer is set
				up, too, although the chunk is marked in use. */
			//在原本的heap的top chunk尾部的空间填入prev_inuse位及标明此chunk大小为0,作为此heap的结尾
			old_size = (old_size - MINSIZE) & ~MALLOC_ALIGN_MASK;
			set_head (chunk_at_offset (old_top, old_size + 2 * SIZE_SZ), 0 | PREV_INUSE);
			//若原本的top chunk分出heap结尾chunk后的size大于chunk的最小size，则设置其head & foot，并free其，将其放入unsorted bin中
			//在old_size -= MINSIZE后依然可用，则在此sub_heap的底部保留一个Min chunk
			if (old_size >= MINSIZE)
			{
				set_head (chunk_at_offset (old_top, old_size), (2 * SIZE_SZ) | PREV_INUSE);
				set_foot (chunk_at_offset (old_top, old_size), (2 * SIZE_SZ));
				set_head (old_top, old_size | PREV_INUSE | NON_MAIN_ARENA);
				_int_free (av, old_top, 1);
			}
			//若空间不够，则仅使用2 * SIZE_SZ大小的空间作为sub_heap结尾标志
			else
			{
				set_head (old_top, (old_size + 2 * SIZE_SZ) | PREV_INUSE);
				set_foot (old_top, (old_size + 2 * SIZE_SZ));
			}
		}
		//*若:1.使用非主分配区分配，当前heap空间不足，增长heap & 创建heap失败
		//*   2.需要分配的size未大于mmap分配阈值
		//*则尝试通过mmap方式分配chunk
		else if (!tried_mmap)
			/* We can at least try to use to mmap memory.	*/
			goto try_mmap;
	}
	//*此处为:
	//*1.各个检测通过
	//*2.分配到main arena
	//*3.mmap流程失败或需分配的chunk size未超过mmap分配阈值
	else
	{ 
		/* Request enough space for nb + pad + overhead */
		//拓展出的部分包含请求的chunk大小，新的top chunk大小和一个最小chunk大小
		size = nb + mp_.top_pad + MINSIZE;

		/*
			If contiguous, we can subtract out existing space that we hope to
			combine with new space. We add it back later only if
			we don't actually get contiguous space.
		*/
		//若main arena的空间连续(一直使用brk分配)
		if (contiguous (av))
			//拓展的大小为新的top chunk和需分配chunk大小减去旧top chunk的大小
			//在结束分配流程后剩余一个top chunk的默认大小作为新的top chunk使用
			size -= old_size;

		/*
			Round to a multiple of page size.
			If MORECORE is not contiguous, this ensures that we only call it
			with whole-page arguments.	And if MORECORE is contiguous and
			this is not first time through, this preserves page-alignment of
			previous calls. Otherwise, we correct to page-align below.
		*/
		//向上对齐到页
		size = ALIGN_UP (size, pagesize);

		/*
			Don't try to call MORECORE if argument is so big as to appear
			negative. Note that since mmap takes size_t arg, it may succeed
			below even if we cannot call MORECORE.
		*/

		if (size > 0)
		{
			//MORECORE宏为一个函数指针，指向__default_morecore函数，其中调用了__sbrk对main arena空间进行了增加
			//增加大小为size，返回指向新增长空间最低地址处的指针
			brk = (char *) (MORECORE (size));
			//*解释如下：
			LIBC_PROBE (memory_sbrk_more, 2, brk, size);
		}
		//每次成功sbrk后执行morecore hook
		if (brk != (char *) (MORECORE_FAILURE))
		{
			/* Call the `morecore' hook if necessary.	*/
			void (*hook) (void) = atomic_forced_read (__after_morecore_hook);
			if (__builtin_expect (hook != NULL, 0))
				(*hook)();
		}
		//*使用主分配区分配，主分配区增长(sbrk)失败
		//*意味着系统中可能存在内存空洞，导致main arena空间无法连续
		else
		{
			/*
				If have mmap, try using it as a backup when MORECORE fails or
				cannot be used. This is worth doing on systems that have "holes" in
				address space, so sbrk cannot extend to give contiguous space, but
				space is available elsewhere.	Note that we ignore mmap max count
				and threshold limits, since the space will not be used as a
				segregated mmap region.
			*/

			//若检测arena仍然为连续，由于之前判断连续性时执行了-old_size操作，此时加上
			//空间不连续，无法合并掉之前的old top chunk区域
			if (contiguous (av))
				size = ALIGN_UP (size + old_size, pagesize);

			/* If we are relying on mmap as backup, then use larger units */
			//最小对main arena的mmap拓展size为1024页
			if ((unsigned long) (size) < (unsigned long) (MMAP_AS_MORECORE_SIZE))
				size = MMAP_AS_MORECORE_SIZE;

			/* Don't try if size wraps around 0 */
			//若新计算出的size大小符合分配需求，则使用mmap对其进行分配
			if ((unsigned long) (size) > (unsigned long) (nb))
			{
				char *mbrk = (char *) (MMAP (0, size, PROT_READ | PROT_WRITE, 0));

				if (mbrk != MAP_FAILED)
				{
					/* We do not need, and cannot use, another sbrk call to find end */
					//调整新的brk指针到mmap区域的地址开始处，snd_brk指针则指向mmap结束位置
					brk = mbrk;
					snd_brk = brk + size;

					/*
						Record that we no longer have a contiguous sbrk region.
						After the first time mmap is used as backup, we do not
						ever rely on contiguous space since this could incorrectly
						bridge regions.
					*/
					//由此，知道main arena的空间连续，设置相关位
					set_noncontiguous (av);
				}
			}
		}

		//主分配区增长成功
		if (brk != (char *) (MORECORE_FAILURE))
		{
			//记录当前brk指针位置，同步arena占用大小量
			if (mp_.sbrk_base == 0)
				mp_.sbrk_base = brk;
			av->system_mem += size;

			/*
				If MORECORE extends previous space, we can likewise extend top size.
			*/
			//*若:1).1.main arena空间增长使用sbrk
			//*      2.或mmap分配未成功(或size不符合要求)
			//*  2).1.且brk指针(新增空间头部)正好位于top chunk尾部位置
			//拓展量为sbrk新增的main arena大小
			if (brk == old_end && snd_brk == (char *) (MORECORE_FAILURE))
				set_head (old_top, (size + old_size) | PREV_INUSE);
			//*此时:1.使用sbrk拓展或未成功使用mmap拓展
			//*    2.且brk位于top chunk尾部前方
			//*    3.且原本的top chunk尚未用完
			else if (contiguous (av) && old_size && brk < old_end)
			/* Oops!	Someone else killed our space..	Can't touch anything.	*/
				malloc_printerr ("break adjusted to free malloc space");

					/*
						Otherwise, make adjustments:

					* If the first time through or noncontiguous, we need to call sbrk
							just to find out where the end of memory lies.

					* We need to ensure that all returned chunks from malloc will meet
							MALLOC_ALIGNMENT

					* If there was an intervening foreign sbrk, we need to adjust sbrk
							request size to account for fact that we will not be able to
							combine new space with existing space in old_top.

					* Almost all systems internally allocate whole pages at a time, in
							which case we might as well use the whole last page of request.
							So we allocate enough more memory to hit a page boundary now,
							which in turn causes future contiguous calls to page-align.
					*/
			//*若:1).1.brk指针未指向top chunk的尾部 (!!!)
			//*      2.或使用mmap增长main arena空间成功(non_contiguous)
			//*且:2).1.原本的top chunk尚存剩余空间
			//*      2.或brk指针位置存在问题
			else
			{
				front_misalign = 0;
				end_misalign = 0;
				correction = 0;
				aligned_brk = brk;

				/* handle contiguous cases */
				//*此处:1).brk指针未指向top chunk尾部，而是位于其高地址处
				//*  且:2).1.未成功使用mmap增长内存
				//*        2.或使用sbrk增长内存
				if (contiguous (av))
				{
					/* Count foreign sbrk as system_mem.	*/
					//*计算brk和top chunk尾部之间的未知空间
					if (old_size)
						av->system_mem += brk - old_end;

					/* Guarantee alignment of first new chunk made from this space */
					//检查brk指针相对于2 * SIZE_SZ的对齐偏移量
					front_misalign = (INTERNAL_SIZE_T) chunk2mem (brk) & MALLOC_ALIGN_MASK;
					//若存在偏移，则修正偏移量，将brk向高地址处修正
					if (front_misalign > 0)
					{
						/*
							Skip over some bytes to arrive at an aligned position.
							We don't need to specially mark these wasted front bytes.
							They will never be accessed anyway because
							prev_inuse of av->top (and any chunk created from its start)
							is always true after initialization.
						*/
						//不需要访问这部分未对齐空间，形成内存碎片(极小量)
						//记录brk指针修正偏移量
						correction = MALLOC_ALIGNMENT - front_misalign;
						aligned_brk += correction;
					}

					/*
						If this isn't adjacent to existing space, then we will not
						be able to merge with old_top space, so must add to 2nd request.
					*/

					correction += old_size;

					/* Extend the end address to hit a page boundary */
					//再次请求的空间尾部指向：
					//1.brk向高地址处对齐到2 * SIZE_SZ
					//2.brk向高地址处移动需求chunk的size + 当前top chunk的size
					//2.brk向高地址处对其到1page
					end_misalign = (INTERNAL_SIZE_T) (brk + size + correction);
					correction += (ALIGN_UP (end_misalign, pagesize)) - end_misalign;

					assert (correction >= 0);
					snd_brk = (char *) (MORECORE (correction));

					/*
						If can't allocate correction, try to at least find out current
						brk.	It might be enough to proceed without failing.

						Note that if second sbrk did NOT fail, we assume that space
						is contiguous with first sbrk. This is a safe assumption unless
						program is multithreaded but doesn't use locks and a foreign sbrk
						occurred between our first and second calls.
					*/
					//得到MORECORE空间最高地址处指针
					if (snd_brk == (char *) (MORECORE_FAILURE))
					{
						correction = 0;
						snd_brk = (char *) (MORECORE (0));
					}
					//增长成功，执行hook
					else
					{
						/* Call the `morecore' hook if necessary.	*/
						void (*hook) (void) = atomic_forced_read (__after_morecore_hook);
						if (__builtin_expect (hook != NULL, 0))
							(*hook)();
					}
				}

				/* handle non-contiguous cases */
				//*成功使用mmap增长内存 or 之前采用过mmap分配main arena内存
				else
				{
					//对齐brk指针
					if (MALLOC_ALIGNMENT == 2 * SIZE_SZ)
						/* MORECORE/mmap must correctly align */
						assert (((unsigned long) chunk2mem (brk) & MALLOC_ALIGN_MASK) == 0);
					else
					{
						front_misalign = (INTERNAL_SIZE_T) chunk2mem (brk) & MALLOC_ALIGN_MASK;
						if (front_misalign > 0)
						{
							/*
								Skip over some bytes to arrive at an aligned position.
								We don't need to specially mark these wasted front bytes.
								They will never be accessed anyway because
								prev_inuse of av->top (and any chunk created from its start)
								is always true after initialization.
							*/

							aligned_brk += MALLOC_ALIGNMENT - front_misalign;
						}
					}

					/* Find out current end of memory */
					//MORECORE(0)得到当前MORECORE分配区域的最高地址处
					if (snd_brk == (char *) (MORECORE_FAILURE))
					{
						snd_brk = (char *) (MORECORE (0));
					}
				}

				/* Adjust top based on results of second sbrk */
				//通过之前计算得到的MORECORE分配区域最高地址处指针snd_brk来调整top chunk
				if (snd_brk != (char *) (MORECORE_FAILURE))
				{
					//将新的top chunk定位在原brk指针向高地址处对齐后的位置
					//并将其size改为其头部到MORECORE分配空间的尾部中间的所有空间
					av->top = (mchunkptr) aligned_brk;
					set_head (av->top, (snd_brk - aligned_brk + correction) | PREV_INUSE);
					av->system_mem += correction;

					/*
						If not the first time through, we either have a
						gap due to foreign sbrk or a non-contiguous region.	Insert a
						double fencepost at old_top to prevent consolidation with space
						we don't own. These fenceposts are artificial chunks that are
						marked as inuse and are in any case too small to use.	We need
						two to make sizes and alignments work out.
					*/

					if (old_size != 0)
					{
						/*
							Shrink old_top to insert fenceposts, keeping size a
							multiple of MALLOC_ALIGNMENT. We know there is at least
							enough space in old_top to do this.
						*/
						//若top chunk有足够的空间，则分出两个2 * SIZE_SZ大小的chunk进行隔离
						old_size = (old_size - 4 * SIZE_SZ) & ~MALLOC_ALIGN_MASK;
						set_head (old_top, old_size | PREV_INUSE);

						/*
							Note that the following assignments completely overwrite
							old_top when old_size was previously MINSIZE.	This is
							intentional. We need the fencepost, even if old_top otherwise gets
							lost.
						*/
						set_head (chunk_at_offset (old_top, old_size),
								(2 * SIZE_SZ) | PREV_INUSE);
						set_head (chunk_at_offset (old_top, old_size + 2 * SIZE_SZ),
								(2 * SIZE_SZ) | PREV_INUSE);

						/* If possible, release the rest. */
						if (old_size >= MINSIZE)
						{
							_int_free (av, old_top, 1);
						}
					}
				}
			}
		}
	} /* if (av !=	&main_arena) */

	if ((unsigned long) av->system_mem > (unsigned long) (av->max_system_mem))
		av->max_system_mem = av->system_mem;
	check_malloc_state (av);

	/* finally, do the allocation */
	p = av->top;
	size = chunksize (p);

	/* check that one of the above allocation paths succeeded */
	if ((unsigned long) (size) >= (unsigned long) (nb + MINSIZE))
	{
		remainder_size = size - nb;
		remainder = chunk_at_offset (p, nb);
		av->top = remainder;
		set_head (p, nb | PREV_INUSE | (av != &main_arena ? NON_MAIN_ARENA : 0));
		set_head (remainder, remainder_size | PREV_INUSE);
		check_malloced_chunk (av, p, nb);
		return chunk2mem (p);
	}

	/* catch all failure paths */
	__set_errno (ENOMEM);
	return 0;
}


/*
	systrim is an inverse of sorts to sysmalloc.	It gives memory back
	to the system (via negative arguments to sbrk) if there is unused
	memory at the `high' end of the malloc pool. It is called
	automatically by free() when top space exceeds the trim
	threshold. It is also called by the public malloc_trim routine.	It
	returns 1 if it actually released any memory, else 0.
 */

static int
systrim (size_t pad, mstate av)
{
	long top_size;				/* Amount of top-most memory */
	long extra;						/* Amount to release */
	long released;				/* Amount actually released */
	char *current_brk;		/* address returned by pre-check sbrk call */
	char *new_brk;				/* address returned by post-check sbrk call */
	size_t pagesize;
	long top_area;

	pagesize = GLRO (dl_pagesize);
	top_size = chunksize (av->top);

	top_area = top_size - MINSIZE - 1;
	if (top_area <= pad)
		return 0;

	/* Release in pagesize units and round down to the nearest page.	*/
	extra = ALIGN_DOWN(top_area - pad, pagesize);

	if (extra == 0)
		return 0;

	/*
		Only proceed if end of memory is where we last set it.
		This avoids problems if there were foreign sbrk calls.
	*/
	current_brk = (char *) (MORECORE (0));
	if (current_brk == (char *) (av->top) + top_size)
		{
			/*
				Attempt to release memory. We ignore MORECORE return value,
				and instead call again to find out where new end of memory is.
				This avoids problems if first call releases less than we asked,
				of if failure somehow altered brk value. (We could still
				encounter problems if it altered brk in some very bad way,
				but the only thing we can do is adjust anyway, which will cause
				some downstream failure.)
			*/

			MORECORE (-extra);
			/* Call the `morecore' hook if necessary.	*/
			void (*hook) (void) = atomic_forced_read (__after_morecore_hook);
			if (__builtin_expect (hook != NULL, 0))
				(*hook)();
			new_brk = (char *) (MORECORE (0));

			LIBC_PROBE (memory_sbrk_less, 2, new_brk, extra);

			if (new_brk != (char *) MORECORE_FAILURE)
				{
					released = (long) (current_brk - new_brk);

					if (released != 0)
						{
							/* Success. Adjust top. */
							av->system_mem -= released;
							set_head (av->top, (top_size - released) | PREV_INUSE);
							check_malloc_state (av);
							return 1;
						}
				}
		}
	return 0;
}

static void
munmap_chunk (mchunkptr p)
{
	INTERNAL_SIZE_T size = chunksize (p);

	assert (chunk_is_mmapped (p));

	/* Do nothing if the chunk is a faked mmapped chunk in the dumped
		main arena.	We never free this memory.	*/
	if (DUMPED_MAIN_ARENA_CHUNK (p))
		return;

	uintptr_t block = (uintptr_t) p - prev_size (p);
	size_t total_size = prev_size (p) + size;
	/* Unfortunately we have to do the compilers job by hand here.	Normally
		we would test BLOCK and TOTAL-SIZE separately for compliance with the
		page size.	But gcc does not recognize the optimization possibility
		(in the moment at least) so we combine the two values into one before
		the bit test.	*/
	if (__builtin_expect (((block | total_size) & (GLRO (dl_pagesize) - 1)) != 0, 0))
		malloc_printerr ("munmap_chunk(): invalid pointer");

	atomic_decrement (&mp_.n_mmaps);
	atomic_add (&mp_.mmapped_mem, -total_size);

	/* If munmap failed the process virtual memory address space is in a
		bad shape.	Just leave the block hanging around, the process will
		terminate shortly anyway since not much can be done.	*/
	__munmap ((char *) block, total_size);
}

#if HAVE_MREMAP

static mchunkptr
mremap_chunk (mchunkptr p, size_t new_size)
{
	size_t pagesize = GLRO (dl_pagesize);
	INTERNAL_SIZE_T offset = prev_size (p);
	INTERNAL_SIZE_T size = chunksize (p);
	char *cp;

	assert (chunk_is_mmapped (p));
	assert (((size + offset) & (GLRO (dl_pagesize) - 1)) == 0);

	/* Note the extra SIZE_SZ overhead as in mmap_chunk(). */
	new_size = ALIGN_UP (new_size + offset + SIZE_SZ, pagesize);

	/* No need to remap if the number of pages does not change.	*/
	if (size + offset == new_size)
		return p;

	cp = (char *) __mremap ((char *) p - offset, size + offset, new_size,
													MREMAP_MAYMOVE);

	if (cp == MAP_FAILED)
		return 0;

	p = (mchunkptr) (cp + offset);

	assert (aligned_OK (chunk2mem (p)));

	assert (prev_size (p) == offset);
	set_head (p, (new_size - offset) | IS_MMAPPED);

	INTERNAL_SIZE_T new;
	new = atomic_exchange_and_add (&mp_.mmapped_mem, new_size - size - offset)
				+ new_size - size - offset;
	atomic_max (&mp_.max_mmapped_mem, new);
	return p;
}
#endif /* HAVE_MREMAP */

/*------------------------ Public wrappers. --------------------------------*/

#if USE_TCACHE

/* We overlay this structure on the user-data portion of a chunk when
	the chunk is stored in the per-thread cache.	*/
typedef struct tcache_entry			//tcache之间的连接通过tcache_entry来完成
{
	struct tcache_entry *next;		//其中保存一个字段，即下一个tcache_entry的指针
} tcache_entry;

/* There is one of these for each thread, which contains the
	per-thread cache (hence "tcache_perthread_struct").	Keeping
	overall size low is mildly important.	Note that COUNTS and ENTRIES
	are redundant (we could have just counted the linked list each
	time), this is for performance reasons.	*/
typedef struct tcache_perthread_struct			//tcache关键结构体
{												//tcache_max_bins为64
	char counts[TCACHE_MAX_BINS];				//记录每个tcache bin中分别有多少tcache的数组
	tcache_entry *entries[TCACHE_MAX_BINS];		//entries指针数组保存每一个tcache bin的第一个tcache的指针
} tcache_perthread_struct;

static __thread bool tcache_shutting_down = false;
static __thread tcache_perthread_struct *tcache = NULL;			//tcache为tcache_perthread_struct结构体的指针，其初始值为NULL

/* Caller must ensure that we know tc_idx is valid and there's room
	for more chunks.	*/
static __always_inline void
tcache_put (mchunkptr chunk, size_t tc_idx)
{
	tcache_entry *e = (tcache_entry *) chunk2mem (chunk);
	assert (tc_idx < TCACHE_MAX_BINS);			//!检测index是否符合tcache
	e->next = tcache->entries[tc_idx];			
	tcache->entries[tc_idx] = e;				//将加入的chunk放到tcache bucket单向链表头部
	++(tcache->counts[tc_idx]);					//增加数量标志
}

/* Caller must ensure that we know tc_idx is valid and there's
	available chunks to remove.	*/
static __always_inline void *
tcache_get (size_t tc_idx)
{
	tcache_entry *e = tcache->entries[tc_idx];	//获取对应tcache bin的入口指针
	assert (tc_idx < TCACHE_MAX_BINS);			//再次检查index大小是否符合
	assert (tcache->entries[tc_idx] > 0);		//再次检查tcache bin的对应入口是否合理(指针数据 > 0)
	tcache->entries[tc_idx] = e->next;			//将该保存在tcache_perthread_struct结构体中bin入口指针数组的指针改为被取出tcache的下一个tcache的指针
	--(tcache->counts[tc_idx]);					//对应的修改该tcache bin中的chunk的数量(在tcache_perthread_struct结构体的count数组中)
	return (void *) e;							//返回该tcache的指针
}

static void
tcache_thread_shutdown (void)
{
	int i;
	tcache_perthread_struct *tcache_tmp = tcache;

	if (!tcache)
		return;

	/* Disable the tcache and prevent it from being reinitialized.	*/
	tcache = NULL;
	tcache_shutting_down = true;

	/* Free all of the entries and the tcache itself back to the arena
		heap for coalescing.	*/
	
	for (i = 0; i < TCACHE_MAX_BINS; ++i)
		{
			while (tcache_tmp->entries[i])
	{
		tcache_entry *e = tcache_tmp->entries[i];
		tcache_tmp->entries[i] = e->next;
		__libc_free (e);
	}
		}

	__libc_free (tcache_tmp);
}

static void
tcache_init(void)
{
	mstate ar_ptr;
	void *victim = 0;
	const size_t bytes = sizeof (tcache_perthread_struct);

	if (tcache_shutting_down)					//再次检测tcache是否开启，若没开启则直接不初始化返回
		return;

	arena_get (ar_ptr, bytes);					//获得一个分配区,其中立即需要使用的mem为bytes大小(无实际作用，hint)
	victim = _int_malloc (ar_ptr, bytes);		//通过_int_malloc分配一个chunk给tcache_perthread_struct使用
	if (!victim && ar_ptr != NULL)				//若分配区成功获取，但是chunk未分配
		{
			ar_ptr = arena_get_retry (ar_ptr, bytes);	//获取另外的分配区入口，重新分配chunk
			victim = _int_malloc (ar_ptr, bytes);
		}


	if (ar_ptr != NULL)
		__libc_lock_unlock (ar_ptr->mutex);				//解开锁

	/* In a low memory situation, we may not be able to allocate memory
		- in which case, we just keep trying later.	However, we
		typically do this very early, so either there is sufficient
		memory, or there isn't enough memory to do non-trivial
		allocations anyway.	*/
	if (victim)													//若成功分配了chunk
		{
			tcache = (tcache_perthread_struct *) victim;			//将chunk指针的传递给tcache
			memset (tcache, 0, sizeof (tcache_perthread_struct));	//初始化内存空间，tcache初始化完成
		}

}

# define MAYBE_INIT_TCACHE() \
	if (__glibc_unlikely (tcache == NULL)) \	//若没有初始化tcache，则tcache为NULL，则直接对其初始化
		tcache_init();							//tcache为tcache_perthread_struct结构体的指针
												//若没有初始化tcache，则结构体没有创建，该指针为空
#else	/* !USE_TCACHE */
# define MAYBE_INIT_TCACHE()					//若初始化了，则什么也不做，返回，开始使用tcache

static void
tcache_thread_shutdown (void)
{
	/* Nothing to do if there is no thread cache.	*/
}

#endif /* !USE_TCACHE	*/


//malloc流程开始

void * __libc_malloc (size_t bytes)		//请求大小
{
	//malloc state结构体指针，指向一个arena
	mstate ar_ptr;
	//暂时为void指针，实际为选择到的chunk指针
	void *victim;
	//malloc hook函数读取与执行操作
	void *(*hook) (size_t, const void *) = atomic_forced_read (__malloc_hook);
	if (__builtin_expect (hook != NULL, 0))
		return (*hook)(bytes, RETURN_ADDRESS (0));
//若使用tcache
#if USE_TCACHE
	/* int_free also calls request2size, be careful to not pad twice.	*/
	//实际chunk size
	size_t tbytes;
	checked_request2size (bytes, tbytes);
	//计算出对应的tcache index， (去掉普通chunk前4个字段)
	size_t tc_idx = csize2tidx (tbytes);
	//进入函数，检测是否已经完成了tcache初始化，若没有，则对其初始化
	MAYBE_INIT_TCACHE ();

	DIAG_PUSH_NEEDS_COMMENT;
	//若:1.通过size计算出的tcache index在tcache的范围之内
	//   2.tcache已初始化
	//   3.request对应的tcache bin中存在tcache
	//若都满足，则获取这个tcache，返回用户指针(直接使用整个chunk，不存在结构性字段)
	if (tc_idx < mp_.tcache_bins
			/*&& tc_idx < TCACHE_MAX_BINS*/ /* to appease gcc */
			&& tcache
			&& tcache->entries[tc_idx] != NULL)
	{
		return tcache_get (tc_idx);
	}
	DIAG_POP_NEEDS_COMMENT;
#endif

	//若无对应大小的tcache，或USE_TCACHE为false，则继续执行，直接使用bin进行分配
	//*若为单线程
	if (SINGLE_THREAD_P)
	{
		//调用_int_malloc获取对应大小的chunk
		victim = _int_malloc (&main_arena, bytes);
		//若该chunk：1.被分配了 2.不是mmap分配的 3.也不在main arena中，说明存在问题，报错
		assert (!victim || chunk_is_mmapped (mem2chunk (victim)) ||
			&main_arena == arena_for_chunk (mem2chunk (victim)));
		//否则则返回用户指针
		return victim;
	}
	//*若非单线程，则首先获取分配区，再调用_int_malloc申请chunk
	arena_get (ar_ptr, bytes);
	victim = _int_malloc (ar_ptr, bytes);
	/* Retry with another arena only if we were able to find a usable arena
		before.	*/
	//分配区获取成功但未分配成功chunk
	if (!victim && ar_ptr != NULL)
	{
		LIBC_PROBE (memory_malloc_retry, 1, bytes);
		//再次尝试获取分配区
		ar_ptr = arena_get_retry (ar_ptr, bytes);
		//随后尝试分配chunk
		victim = _int_malloc (ar_ptr, bytes);
	}
	//若分配区获取成功，解除分配区互斥锁
	if (ar_ptr != NULL)
		__libc_lock_unlock (ar_ptr->mutex);
	//若该chunk：1.被分配了 2.不是mmap分配的 3.也不在该分配区中；说明存在问题，报错
	assert (!victim || chunk_is_mmapped (mem2chunk (victim)) ||
					ar_ptr == arena_for_chunk (mem2chunk (victim)));
	return victim;
}
libc_hidden_def (__libc_malloc)

void
__libc_free (void *mem)
{
	mstate ar_ptr;
	mchunkptr p;													/* chunk corresponding to mem */
	//若free hook已设定，先执行free hook
	//free hook以free的chunk中的数据为第一个参数
	void (*hook) (void *, const void *)
		= atomic_forced_read (__free_hook);
	if (__builtin_expect (hook != NULL, 0))
	{
		(*hook)(mem, RETURN_ADDRESS (0));
		return;
	}
	//free(0)不产生任何作用
	if (mem == 0)
		return;
	//转换指针，得到chunk头指针
	p = mem2chunk (mem);
	//判断chunk状态是否为mmaped
	if (chunk_is_mmapped (p))											/* release mmapped memory. */
	{
		/* See if the dynamic brk/mmap threshold needs adjusting.
		Dumped fake mmapped chunks do not affect the threshold.	*/
		//*条件:1.启动动态分配阈值调整
		//*    2.chunk大小大于当前ptmalloc的mmap动态分配阈值
		//*    3.chunk大小小于mmap最大分配空间量
		//*    4.chunk位置位于main arena外部
		//*则 :1.将ptmalloc的mmap分配阈值调整至此chunk大小
		//*    2.将ptmalloc的arena收缩阈值调整至mmap分配阈值的两倍
		if (!mp_.no_dyn_threshold
				&& chunksize_nomask (p) > mp_.mmap_threshold
				&& chunksize_nomask (p) <= DEFAULT_MMAP_THRESHOLD_MAX
				&& !DUMPED_MAIN_ARENA_CHUNK (p))
		{
			mp_.mmap_threshold = chunksize (p);
			mp_.trim_threshold = 2 * mp_.mmap_threshold;
			LIBC_PROBE (memory_mallopt_free_dyn_thresholds, 2,
									mp_.mmap_threshold, mp_.trim_threshold);
		}
		//释放这个chunk，并返回
		munmap_chunk (p);
		return;
	}

	MAYBE_INIT_TCACHE ();
	//*若该chunk不是mmapedchunk，则查找其所属arena，通过_int_free函数释放
	ar_ptr = arena_for_chunk (p);
	_int_free (ar_ptr, p, 0);
}
libc_hidden_def (__libc_free)

void *
__libc_realloc (void *oldmem, size_t bytes)
{
	mstate ar_ptr;
	INTERNAL_SIZE_T nb;				/* padded request size */

	void *newp;						/* chunk to return */

	void *(*hook) (void *, size_t, const void *) =
		atomic_forced_read (__realloc_hook);
	if (__builtin_expect (hook != NULL, 0))
		return (*hook)(oldmem, bytes, RETURN_ADDRESS (0));

#if REALLOC_ZERO_BYTES_FREES
	if (bytes == 0 && oldmem != NULL)
		{
			__libc_free (oldmem); return 0;
		}
#endif

	/* realloc of null is supposed to be same as malloc */
	if (oldmem == 0)
		return __libc_malloc (bytes);

	/* chunk corresponding to oldmem */
	const mchunkptr oldp = mem2chunk (oldmem);
	/* its size */
	const INTERNAL_SIZE_T oldsize = chunksize (oldp);

	if (chunk_is_mmapped (oldp))
		ar_ptr = NULL;
	else
		{
			MAYBE_INIT_TCACHE ();
			ar_ptr = arena_for_chunk (oldp);
		}

	/* Little security check which won't hurt performance: the allocator
		never wrapps around at the end of the address space.	Therefore
		we can exclude some size values which might appear here by
		accident or by "design" from some intruder.	We need to bypass
		this check for dumped fake mmap chunks from the old main arena
		because the new malloc may provide additional alignment.	*/
	if ((__builtin_expect ((uintptr_t) oldp > (uintptr_t) -oldsize, 0)
			|| __builtin_expect (misaligned_chunk (oldp), 0))
			&& !DUMPED_MAIN_ARENA_CHUNK (oldp))
			malloc_printerr ("realloc(): invalid pointer");

	checked_request2size (bytes, nb);

	if (chunk_is_mmapped (oldp))
		{
			/* If this is a faked mmapped chunk from the dumped main arena,
	always make a copy (and do not free the old chunk).	*/
			if (DUMPED_MAIN_ARENA_CHUNK (oldp))
	{
		/* Must alloc, copy, free. */
		void *newmem = __libc_malloc (bytes);
		if (newmem == 0)
			return NULL;
		/* Copy as many bytes as are available from the old chunk
			and fit into the new size.	NB: The overhead for faked
			mmapped chunks is only SIZE_SZ, not 2 * SIZE_SZ as for
			regular mmapped chunks.	*/
		if (bytes > oldsize - SIZE_SZ)
			bytes = oldsize - SIZE_SZ;
		memcpy (newmem, oldmem, bytes);
		return newmem;
	}

			void *newmem;

#if HAVE_MREMAP
			newp = mremap_chunk (oldp, nb);
			if (newp)
				return chunk2mem (newp);
#endif
			/* Note the extra SIZE_SZ overhead. */
			if (oldsize - SIZE_SZ >= nb)
				return oldmem;												/* do nothing */

			/* Must alloc, copy, free. */
			newmem = __libc_malloc (bytes);
			if (newmem == 0)
				return 0;							/* propagate failure */

			memcpy (newmem, oldmem, oldsize - 2 * SIZE_SZ);
			munmap_chunk (oldp);
			return newmem;
		}

	if (SINGLE_THREAD_P)
		{
			newp = _int_realloc (ar_ptr, oldp, oldsize, nb);
			assert (!newp || chunk_is_mmapped (mem2chunk (newp)) ||
				ar_ptr == arena_for_chunk (mem2chunk (newp)));

			return newp;
		}

	__libc_lock_lock (ar_ptr->mutex);

	newp = _int_realloc (ar_ptr, oldp, oldsize, nb);

	__libc_lock_unlock (ar_ptr->mutex);
	assert (!newp || chunk_is_mmapped (mem2chunk (newp)) ||
					ar_ptr == arena_for_chunk (mem2chunk (newp)));

	if (newp == NULL)
		{
			/* Try harder to allocate memory in other arenas.	*/
			LIBC_PROBE (memory_realloc_retry, 2, bytes, oldmem);
			newp = __libc_malloc (bytes);
			if (newp != NULL)
				{
					memcpy (newp, oldmem, oldsize - SIZE_SZ);
					_int_free (ar_ptr, oldp, 0);
				}
		}

	return newp;
}
libc_hidden_def (__libc_realloc)

void *
__libc_memalign (size_t alignment, size_t bytes)
{
	void *address = RETURN_ADDRESS (0);
	return _mid_memalign (alignment, bytes, address);
}

static void *
_mid_memalign (size_t alignment, size_t bytes, void *address)
{
	mstate ar_ptr;
	void *p;

	void *(*hook) (size_t, size_t, const void *) =
		atomic_forced_read (__memalign_hook);
	if (__builtin_expect (hook != NULL, 0))
		return (*hook)(alignment, bytes, address);

	/* If we need less alignment than we give anyway, just relay to malloc.	*/
	if (alignment <= MALLOC_ALIGNMENT)
		return __libc_malloc (bytes);

	/* Otherwise, ensure that it is at least a minimum chunk size */
	if (alignment < MINSIZE)
		alignment = MINSIZE;

	/* If the alignment is greater than SIZE_MAX / 2 + 1 it cannot be a
		power of 2 and will cause overflow in the check below.	*/
	if (alignment > SIZE_MAX / 2 + 1)
		{
			__set_errno (EINVAL);
			return 0;
		}

	/* Check for overflow.	*/
	if (bytes > SIZE_MAX - alignment - MINSIZE)
		{
			__set_errno (ENOMEM);
			return 0;
		}


	/* Make sure alignment is power of 2.	*/
	if (!powerof2 (alignment))
		{
			size_t a = MALLOC_ALIGNMENT * 2;
			while (a < alignment)
				a <<= 1;
			alignment = a;
		}

	if (SINGLE_THREAD_P)
		{
			p = _int_memalign (&main_arena, alignment, bytes);
			assert (!p || chunk_is_mmapped (mem2chunk (p)) ||
				&main_arena == arena_for_chunk (mem2chunk (p)));

			return p;
		}

	arena_get (ar_ptr, bytes + alignment + MINSIZE);

	p = _int_memalign (ar_ptr, alignment, bytes);
	if (!p && ar_ptr != NULL)
		{
			LIBC_PROBE (memory_memalign_retry, 2, bytes, alignment);
			ar_ptr = arena_get_retry (ar_ptr, bytes);
			p = _int_memalign (ar_ptr, alignment, bytes);
		}

	if (ar_ptr != NULL)
		__libc_lock_unlock (ar_ptr->mutex);

	assert (!p || chunk_is_mmapped (mem2chunk (p)) ||
					ar_ptr == arena_for_chunk (mem2chunk (p)));
	return p;
}
/* For ISO C11.	*/
weak_alias (__libc_memalign, aligned_alloc)
libc_hidden_def (__libc_memalign)

void *
__libc_valloc (size_t bytes)
{
	if (__malloc_initialized < 0)
		ptmalloc_init ();

	void *address = RETURN_ADDRESS (0);
	size_t pagesize = GLRO (dl_pagesize);
	return _mid_memalign (pagesize, bytes, address);
}

void *
__libc_pvalloc (size_t bytes)
{
	if (__malloc_initialized < 0)
		ptmalloc_init ();

	void *address = RETURN_ADDRESS (0);
	size_t pagesize = GLRO (dl_pagesize);
	size_t rounded_bytes = ALIGN_UP (bytes, pagesize);

	/* Check for overflow.	*/
	if (bytes > SIZE_MAX - 2 * pagesize - MINSIZE)
		{
			__set_errno (ENOMEM);
			return 0;
		}

	return _mid_memalign (pagesize, rounded_bytes, address);
}

void *
__libc_calloc (size_t n, size_t elem_size)
{
	mstate av;
	mchunkptr oldtop, p;
	INTERNAL_SIZE_T bytes, sz, csz, oldtopsize;
	void *mem;
	unsigned long clearsize;
	unsigned long nclears;
	INTERNAL_SIZE_T *d;

	/* size_t is unsigned so the behavior on overflow is defined.	*/
	bytes = n * elem_size;
#define HALF_INTERNAL_SIZE_T \
	(((INTERNAL_SIZE_T) 1) << (8 * sizeof (INTERNAL_SIZE_T) / 2))
	if (__builtin_expect ((n | elem_size) >= HALF_INTERNAL_SIZE_T, 0))
		{
			if (elem_size != 0 && bytes / elem_size != n)
				{
					__set_errno (ENOMEM);
					return 0;
				}
		}

	void *(*hook) (size_t, const void *) =
		atomic_forced_read (__malloc_hook);
	if (__builtin_expect (hook != NULL, 0))
		{
			sz = bytes;
			mem = (*hook)(sz, RETURN_ADDRESS (0));
			if (mem == 0)
				return 0;

			return memset (mem, 0, sz);
		}

	sz = bytes;

	MAYBE_INIT_TCACHE ();

	if (SINGLE_THREAD_P)
		av = &main_arena;
	else
		arena_get (av, sz);

	if (av)
		{
			/* Check if we hand out the top chunk, in which case there may be no
	need to clear. */
#if MORECORE_CLEARS
			oldtop = top (av);
			oldtopsize = chunksize (top (av));
# if MORECORE_CLEARS < 2
			/* Only newly allocated memory is guaranteed to be cleared.	*/
			if (av == &main_arena &&
		oldtopsize < mp_.sbrk_base + av->max_system_mem - (char *) oldtop)
	oldtopsize = (mp_.sbrk_base + av->max_system_mem - (char *) oldtop);
# endif
			if (av != &main_arena)
	{
		heap_info *heap = heap_for_ptr (oldtop);
		if (oldtopsize < (char *) heap + heap->mprotect_size - (char *) oldtop)
			oldtopsize = (char *) heap + heap->mprotect_size - (char *) oldtop;
	}
#endif
		}
	else
		{
			/* No usable arenas.	*/
			oldtop = 0;
			oldtopsize = 0;
		}
	mem = _int_malloc (av, sz);

	assert (!mem || chunk_is_mmapped (mem2chunk (mem)) ||
					av == arena_for_chunk (mem2chunk (mem)));

	if (!SINGLE_THREAD_P)
		{
			if (mem == 0 && av != NULL)
	{
		LIBC_PROBE (memory_calloc_retry, 1, sz);
		av = arena_get_retry (av, sz);
		mem = _int_malloc (av, sz);
	}

			if (av != NULL)
	__libc_lock_unlock (av->mutex);
		}

	/* Allocation failed even after a retry.	*/
	if (mem == 0)
		return 0;

	p = mem2chunk (mem);

	/* Two optional cases in which clearing not necessary */
	if (chunk_is_mmapped (p))
		{
			if (__builtin_expect (perturb_byte, 0))
				return memset (mem, 0, sz);

			return mem;
		}

	csz = chunksize (p);

#if MORECORE_CLEARS
	if (perturb_byte == 0 && (p == oldtop && csz > oldtopsize))
		{
			/* clear only the bytes from non-freshly-sbrked memory */
			csz = oldtopsize;
		}
#endif

	/* Unroll clear of <= 36 bytes (72 if 8byte sizes).	We know that
		contents have an odd number of INTERNAL_SIZE_T-sized words;
		minimally 3.	*/
	d = (INTERNAL_SIZE_T *) mem;
	clearsize = csz - SIZE_SZ;
	nclears = clearsize / sizeof (INTERNAL_SIZE_T);
	assert (nclears >= 3);

	if (nclears > 9)
		return memset (d, 0, clearsize);

	else
		{
			*(d + 0) = 0;
			*(d + 1) = 0;
			*(d + 2) = 0;
			if (nclears > 4)
				{
					*(d + 3) = 0;
					*(d + 4) = 0;
					if (nclears > 6)
						{
							*(d + 5) = 0;
							*(d + 6) = 0;
							if (nclears > 8)
								{
									*(d + 7) = 0;
									*(d + 8) = 0;
								}
						}
				}
		}

	return mem;
}

/*
	------------------------------ malloc ------------------------------
 */

static void *
_int_malloc (mstate av, size_t bytes)				//bytes:用户请求的size
{
	INTERNAL_SIZE_T nb;							    //nb:实际需要分配的chunk
	unsigned int idx;								//计算得出的bin index
	mbinptr bin;									//typedef from struct malloc_chunk   //为bin的表头指针

	mchunkptr victim;								//typedef from struct malloc_chunk   //已选定的chunk指针
	INTERNAL_SIZE_T size;						/* its size */
	int victim_index;								/* its bin index */

	mchunkptr remainder;							//last remainer指针
	unsigned long remainder_size;					//last remainer size

	unsigned int block;							/* bit map traverser */
	unsigned int bit;								/* bit map traverser */
	unsigned int map;								/* current word of binmap */

	mchunkptr fwd;										/* misc temp for linking */
	mchunkptr bck;										/* misc temp for linking */

#if USE_TCACHE
	size_t tcache_unsorted_count;			/* count of unsorted chunks processed */
#endif

	/*
		Convert request size to internal form by adding SIZE_SZ bytes
		overhead plus possibly more to obtain necessary alignment and/or
		to obtain a size of at least MINSIZE, the smallest allocatable
		size. Also, checked_request2size traps (returning 0) request sizes
		that are so large that they wrap around zero when padded and
		aligned.
	*/

	checked_request2size (bytes, nb);			//转换chunk size并检查

	//若未获取到arena，则是所有分配区均在使用，则直接使用sysmalloc进行mmap分配内存
	if (__glibc_unlikely (av == NULL))
	{
		void *p = sysmalloc (nb, av);
		if (p != NULL)
			alloc_perturb (p, bytes);
		return p;							//返回得到的mmaped_chunk指针，退出分配流程
	}

	/*
		If the size qualifies as a fastbin, first check corresponding bin.
		This code is safe to execute even if av is not yet initialized, so we
		can try it without checking, which saves some time on this fast path.
	*/

#define REMOVE_FB(fb, victim, pp)			\
	do							\
	{							\
		victim = pp;					\
		if (victim == NULL)				\
		break;						\
	}							\
	while ((pp = catomic_compare_and_exchange_val_acq (fb, victim->fd, victim))!= victim);					\
//* fast chunk分配流程
	if ((unsigned long) (nb) <= (unsigned long) (get_max_fast ()))	//检测实际chunk大小是否位于fast chunk范围内
		{
			/*
			获取fast bin的index
			fastbin index从0开始计，最小大小为4 * SIZE_SZ,以 2 * SIZE_SZ 作为fastbin之间的大小公差
			*/															
			idx = fastbin_index (nb);
													//获取fastbinsY指针数组对应index处的指针(指向对应大小的fast chunk / 或NULL)
			mfastbinptr *fb = &fastbin (av, idx);	//fb为对应fastbinsY表头的引用，fastbinsY的表头为指向对应fastbin中第一个chunk的指针(相当于fd指针)
			mchunkptr pp;
			victim = *fb;							//将即将分配的chunk指针设置为指向对应fastbinsY数组对应位置指向的chunk

			if (victim != NULL)						//对应的fastbin中有chunk，fastbinsY数组中的指针不为NULL
			{
				if (SINGLE_THREAD_P)				//若程序为单线程
					*fb = victim->fd;				//则将该chunk的fd chunk设置为该fast bin表头指向的chunk(表头位于bk指针的尾端)
				else
					REMOVE_FB (fb, pp, victim);		//多线程情况，暂且不论
				if (__glibc_likely (victim != NULL))
				{
					size_t victim_idx = fastbin_index (chunksize (victim));		// !对即将分配的chunk的大小进行检查，看是否与之前的chunk位置对应
					if (__builtin_expect (victim_idx != idx, 0))				// !（无法在中途修改size后继续使用该chunk）
						malloc_printerr ("malloc(): memory corruption (fast)");
					check_remalloced_chunk (av, victim, nb);					//检测，无影响
					#if USE_TCACHE												//若使用tcache
					/* While we're here, if we see other chunks of the same size,	
					stash them in the tcache.	*/
					size_t tc_idx = csize2tidx (nb);							//获取对应大小的tcache index	
					if (tcache && tc_idx < mp_.tcache_bins)						//若tcache已初始化，且之前请求的chunk大小符合tcache的chunk大小
					{
						mchunkptr tc_victim;

						/* While bin not empty and tcache not full, copy chunks.	*/
						while (tcache->counts[tc_idx] < mp_.tcache_count		//若当前tcache bucket中的数量未超过单个tcache bucket中最大数量限制，且fb不为NULL，则循环
							&& (tc_victim = *fb) != NULL)						//将分配了之前chunk的fast bin中的fast chunk放入对应大小的tcache中管理
						{
							if (SINGLE_THREAD_P)
								*fb = tc_victim->fd;
							else
							{
								REMOVE_FB (fb, pp, tc_victim);
								if (__glibc_unlikely (tc_victim == NULL))
									break;
							}
							tcache_put (tc_victim, tc_idx);						//将chunk放入tcache
						}
					}
					#endif
					void *p = chunk2mem (victim);		//将从fastbin中获取到的chunk改为用户使用的mem指针
					alloc_perturb (p, bytes);
					return p;							//返回，分配流程结束
				}
			}
		}

	/*
		If a small request, check regular bin.	Since these "smallbins"
		hold one size each, no searching within bins is necessary.
		(For a large request, we need to wait until unsorted chunks are
		processed to find best fit. But for small ones, fits are exact
		anyway, so we can check now, which is faster.)
	*/
//* small chunk分配流程
//* 若对应的small bin中存在大小合适的chunk，则直接分配
//* 若bin中没有合适大小的chunk，则将计算出的small bin index和对应的bin表头指针记录到idx & bin中
	if (in_smallbin_range (nb))
		{
			idx = smallbin_index (nb);	//nb / (2*SIZE_SZ) 为对应的small bin index
			bin = bin_at (av, idx);		//获取对应bin的头chunk

			if ((victim = last (bin)) != bin)	//若该bin中存在chunk
			{
				bck = victim->bk;
				if (__glibc_unlikely (bck->fd != victim))	//!检测是否存在双向链表指针不符的情况
					malloc_printerr ("malloc(): smallbin double linked list corrupted");
				set_inuse_bit_at_offset (victim, nb);		//设置使用位
				bin->bk = bck;
				bck->fd = bin;								//将victim chunk的下一个chunk与表头直接连接

				if (av != &main_arena)
					set_non_main_arena (victim);			//检测是否为main arena中分配，若不是，则置位
				check_malloced_chunk (av, victim, nb);
				//若条件符合，则将当前分配的small bin中的chunk加入tcache
				#if USE_TCACHE
				/* While we're here, if we see other chunks of the same size,
					stash them in the tcache.	*/
					size_t tc_idx = csize2tidx (nb);
					if (tcache && tc_idx < mp_.tcache_bins)	//若tcache已初始化，且当前分配的chunk大小符合tcache的大小需求
					{
						mchunkptr tc_victim;

						/* While bin not empty and tcache not full, copy chunks over.	*/
						while (tcache->counts[tc_idx] < mp_.tcache_count
						&& (tc_victim = last (bin)) != bin)	//在tcache bucket数量未超过限制且当前bin中尚存chunk时，将chunk放入到tcache中
						{
							if (tc_victim != 0)
							{
								bck = tc_victim->bk;
								set_inuse_bit_at_offset (tc_victim, nb);	//tcache和fastbin chunk in_use位恒为1
								if (av != &main_arena)
									set_non_main_arena (tc_victim);
								bin->bk = bck;
								bck->fd = bin;
								tcache_put (tc_victim, tc_idx);
							}
						}
					}
				#endif
					void *p = chunk2mem (victim);			//转换指针并退出，结束分配流程
					alloc_perturb (p, bytes);
					return p;
			}
		}

	/*
		If this is a large request, consolidate fastbins before continuing.
		While it might look excessive to kill all fastbins before
		even seeing if there is space available, this avoids
		fragmentation problems normally associated with fastbins.
		Also, in practice, programs tend to have runs of either small or
		large requests, but less often mixtures, so consolidation is not
		invoked all that often in most programs. And the programs that
		it is called frequently in otherwise tend to fragment.
	*/
//* large chunk分配预流程
//* 将size 对应的large bin index记录到idx中
//* 执行malloc_consolidate宏，合并可合并的fast chunk并放入unsorted bin中
//* 为后续清理unsorted bin做准备
	//若不在small bins中，则在largebin中查找
	else
	{
		idx = largebin_index (nb);
		if (atomic_load_relaxed (&av->have_fastchunks))
			//对所有fast chunk和前后chunk进行合并，并将合并后的chunk放入unsorted bin中
			malloc_consolidate (av);
	}

	/*
		Process recently freed or remaindered chunks, taking one only if
		it is exact fit, or, if this a small request, the chunk is remainder from
		the most recent non-exact fit.	Place other traversed chunks in
		bins.	Note that this step is the only place in any routine where
		chunks are placed in bins.

		The outer loop here is needed because we might not realize until
		near the end of malloc that we should have consolidated, so must
		do so and retry. This happens at most once, and only when we would
		otherwise need to expand memory to service a "small" request.
	*/
	//*此处，当:
	//*1.需要分配small chunk，但无法在现有的fastbin/smallbin中找到对应大小的chunk
	//*2.或需要分配large chunk的范围时生效
#if USE_TCACHE
	INTERNAL_SIZE_T tcache_nb = 0;
	//请求大小符合tcache的size范围
	size_t tc_idx = csize2tidx (nb);
	if (tcache && tc_idx < mp_.tcache_bins)
		tcache_nb = nb;
	//将tcache中的unsorted数量设置为0
	int return_cached = 0;
	tcache_unsorted_count = 0;
#endif

	for (;; )
	{
		int iters = 0;
		//*在unsorted bin中尚有chunk时循环，循环遍历unsorted bin中的所有chunk
		//*将unsorted bin中的chunk整理入对应的bins
		//*若遇到符合大小的chunk，可记录或直接使用
		while ((victim = unsorted_chunks (av)->bk) != unsorted_chunks (av))
		{
			//bck:unsorted bin链表中后侧相邻的chunk
			bck = victim->bk;
			size = chunksize (victim);
			//next:地址上的后侧相邻chunk
			mchunkptr next = chunk_at_offset (victim, size);
		/*
		此处进行unsorted chunk处理过程中对每个chunk的检测
		!1.检测chunk的size大小是否越界
		!2.检测相邻地址的下一个chunk的size大小是否越界
		!3.检测next chunk的prev_size字段和当前chunk的size字段是否相符
		!4.检测当前chunk的前后指针是否正确无问题
		!5.检测下一个chunk的prev_inuse字段是否为0
		*/
			if (__glibc_unlikely (size <= 2 * SIZE_SZ)
					|| __glibc_unlikely (size > av->system_mem))
				malloc_printerr ("malloc(): invalid size (unsorted)");
			if (__glibc_unlikely (chunksize_nomask (next) < 2 * SIZE_SZ)
					|| __glibc_unlikely (chunksize_nomask (next) > av->system_mem))
				malloc_printerr ("malloc(): invalid next size (unsorted)");
			if (__glibc_unlikely ((prev_size (next) & ~(SIZE_BITS)) != size))
				malloc_printerr ("malloc(): mismatching next->prev_size (unsorted)");
			if (__glibc_unlikely (bck->fd != victim)
					|| __glibc_unlikely (victim->fd != unsorted_chunks (av)))
				malloc_printerr ("malloc(): unsorted double linked list corrupted");
			if (__glibc_unlikely (prev_inuse (next)))
				malloc_printerr ("malloc(): invalid next->prev_inuse (unsorted)");

			/*
				If a small request, try to use last remainder if it is the
				only chunk in unsorted bin.	This helps promote locality for
				runs of consecutive small requests. This is the only
				exception to best-fit, and applies only when there is
				no exact fit for a small chunk.
			*/
			//*此处为1.last_remainder为unsorted bin中的唯一一个chunk
			//*     2.且即将分配的chunk大小小于last_remainder的大小
			//*     3.且size在small size range内
			//切割 last remainder
			if (in_smallbin_range (nb) &&
					bck == unsorted_chunks (av) &&
					victim == av->last_remainder &&
					(unsigned long) (size) > (unsigned long) (nb + MINSIZE))
			{
				//计算切割后的remainder大小
				remainder_size = size - nb;
				//重新确定所有last_remainder指针指向
				//last_remainder的低地址部分被切割出来成为了victim指向的chunk，高低址部分剩下成为新的last_remainder
				remainder = chunk_at_offset (victim, nb);

				//重新排布unsorted bin的双向循环链表&将arena管理结构体malloc_state中指向last_remainder的指针指向新的last remainder
				unsorted_chunks (av)->bk = unsorted_chunks (av)->fd = remainder;
				av->last_remainder = remainder;
				remainder->bk = remainder->fd = unsorted_chunks (av);

				//remainder为large chunk范围时候，设置size指针字段为NULL
				if (!in_smallbin_range (remainder_size))
					{
						remainder->fd_nextsize = NULL;
						remainder->bk_nextsize = NULL;
					}
				
				//设置切割后的victim chunk和last remainder的相应字段
				set_head (victim, nb | PREV_INUSE |
									(av != &main_arena ? NON_MAIN_ARENA : 0));
				//由于victim是last remainder切割出来的，将新的last remainder的prev_inuse位设为1(prev chunk为victim)
				set_head (remainder, remainder_size | PREV_INUSE);
				set_foot (remainder, remainder_size);

				//检测被分配的chunk，并转换指针，退出分配程序
				check_malloced_chunk (av, victim, nb);
				void *p = chunk2mem (victim);
				alloc_perturb (p, bytes);
				return p;
			}
			
			//*此处为:1.unsorted bin中不止一个chunk
			//*      2.或last remainder无法满足small chunk分配需求
			//*      3.或需要分配large chunk时
			//整理unsorted bin中的chunk，将其放入对应的bin或tcache中
			//victim = unsorted_bin(av)->bk
			//bck = victim->bk
			//!链表检测，victim->bk->fd == victim
					/* remove from unsorted list */
			if (__glibc_unlikely (bck->fd != victim))
				malloc_printerr ("malloc(): corrupted unsorted chunks 3");
			//将victim chunk从unsorted bin中unlink出来
			unsorted_chunks (av)->bk = bck;
			bck->fd = unsorted_chunks (av);

			//若该victim chunk size恰好合适，则转换指针后返回使用
			if (size == nb)
			{
				//对与victim地址相邻的下一个chunk设置prev_inuse位
				set_inuse_bit_at_offset (victim, size);
				if (av != &main_arena)
					set_non_main_arena (victim);

			//若启用了tcache，则无论如何现将chunk放入对应的tcache中，在tcache被填满或unsorted bin中chunk被整理完成后再进行分配
			#if USE_TCACHE
				if (tcache_nb
					&& tcache->counts[tc_idx] < mp_.tcache_count)
				{
					tcache_put (victim, tc_idx);
					//设置位，标志tcache中存在可供分配的chunk
					return_cached = 1;
					continue;
				}
				else
				{
			#endif
				//*若启用了tcache，且对应size的tcache bin被放满了，则直接返回该chunk
				//*若unsorted bin中被整理的最后一个chunk满足size需求，则返回该chunk
				//*若未启用tcache，则遇到对应size的chunk时直接转换并返回指针
					check_malloced_chunk (av, victim, nb);
					void *p = chunk2mem (victim);
					alloc_perturb (p, bytes);
					return p;
			#if USE_TCACHE
				}  
			#endif
			}

			/* place chunk in bin */
			//*此处为:1.取到unsorted bin中的最后一个chunk
			//*      2.若未启用tcache，则表明unsorted bin被整理的chunk中没有一个符合size
			//*		 3.若启用了tcache，可能部分size符合的chunk被放入了tcache中
			//victim为small chunk，则将chunk放入链表尾部，记录指针
			//victim为large chunk，则设置size指针，记录fd & bk指针
			if (in_smallbin_range (size))
			{
				victim_index = smallbin_index (size);
				//设置bck为表头，fwd为bin链表中最后一项
				bck = bin_at (av, victim_index);
				fwd = bck->fd;
			}
			//*large bin chunk的size从bin中的第一个chunk到最后一个chunk为递减趋势
			else
			{
				victim_index = largebin_index (size);
				bck = bin_at (av, victim_index);
				fwd = bck->fd;
				/* maintain large bins in sorted order */
				//若large bin链表中已存在chunks
				if (fwd != bck)
				{
					/* Or with inuse bit to speed comparisons */
					//设置prev_inuse位
					size |= PREV_INUSE;
					/* if smaller than smallest, bypass loop below */
					//!检测bin中的最后一个chunk(最小的chunk)是否为main_arena分配的
					assert (chunk_main_arena (bck->bk));
					//*若victim size小于large bin中的最后一个chunk，则：
					//*将victim chunk放在large bin的最后
					if ((unsigned long) (size)
						< (unsigned long) chunksize_nomask (bck->bk))
					{
						//设置victim chunk及其bin中前后large chunk中的size指针
						fwd = bck;
						bck = bck->bk;
						victim->fd_nextsize = fwd->fd;
						victim->bk_nextsize = fwd->fd->bk_nextsize;
						fwd->fd->bk_nextsize = victim->bk_nextsize->fd_nextsize = victim;
					}
					else
					{
						//!检测bin中第一个chunk是否为main arena分配的
						assert (chunk_main_arena (fwd));
						//从大到小遍历bin中相同大小chunk中的第一个chunk，并检测该chunk是否为main arena分配的
						//当找到一个size和victim同样大(设置了prev_inuse位，相当于size += 1)或者比victim小的chunk时，停在bin链表中该chunk的前方
						//将该chunk放入到相同size的chunk中的第一个位置
						while ((unsigned long) size < chunksize_nomask (fwd))
						{
							fwd = fwd->fd_nextsize;
							assert (chunk_main_arena (fwd));
						}
						//若size和fwd的size恰好相等(由于size += 1，几乎不可能)
						if ((unsigned long) size
							== (unsigned long) chunksize_nomask (fwd))
							/* Always insert in the second position.	*/
							fwd = fwd->fd;
						//调整相关指针
						else
						{
							victim->fd_nextsize = fwd;
							victim->bk_nextsize = fwd->bk_nextsize;
							fwd->bk_nextsize = victim;
							victim->bk_nextsize->fd_nextsize = victim;
						}
						//记录插入位置前后chunk的指针
						bck = fwd->bk;
					}
				}
				//bin中无chunk，直接放入
				else
					victim->fd_nextsize = victim->bk_nextsize = victim;
			}
			//*此处，chunk的fd & bk指针已确定完成，分别是fwd & bck，可直接放入对应的bin中
			//设置对应bin的binmap，标志其正在使用
			mark_bin (av, victim_index);
			victim->bk = bck;
			victim->fd = fwd;
			fwd->bk = victim;
			bck->fd = victim;

			/* If we've processed as many chunks as we're allowed while
				filling the cache, return one of the cached ones.	*/
			#if USE_TCACHE
				++tcache_unsorted_count;
				//若tcache中放入了合适size的chunk，且超出了tcache记录的unsorted chunk的收纳上限(收纳到任何地方都进行记录)，则获取一个合适大小的tcache并返回
				if (return_cached
					&& mp_.tcache_unsorted_limit > 0
					&& tcache_unsorted_count > mp_.tcache_unsorted_limit)
				{
					return tcache_get (tc_idx);
				}
			#endif

		//若超过最大unsorted chunk处理限制，则退出继续处理unsorted chunk的流程(保证单个chunk分配效率)
			#define MAX_ITERS			10000
			if (++iters >= MAX_ITERS)
				break;
		}

		#if USE_TCACHE
			/* If all the small chunks we found ended up cached, return one now.	*/
			//若之前处理unsorted chunk的过程中有符合victim size的chunk被放入了tcache中，则在此处对其分配
			if (return_cached)
			{
				return tcache_get (tc_idx);
			}
		#endif

		/*
			If a large request, scan through the chunks of current bin in
			sorted order to find smallest that fits.	Use the skip list for this.
		*/
		//*此处，unsorted chunk处理流程完成
		//*没有找到恰好符合大小的chunk，且bin中存在从unsorted bin中整理出的chunks
		//*此时需求的chunk size若在small chunk范围内，则已经无法直接通过best-fit原则从small bin中找到了
		//*而若在large chunk范围内，则执行以下流程
		if (!in_smallbin_range (nb))
		{
			//找出size所对应的bin表头
			bin = bin_at (av, idx);

			/* skip scan if empty or largest chunk is too small */
			//*若:
			//*1.bin中有chunk
			//*2.且bin中最大的chunk的size大于需要分配的chunk size
			//*则可以在该bin中执行分配chunk的流程
			if ((victim = first (bin)) != bin
				&& (unsigned long) chunksize_nomask (victim)
				>= (unsigned long) (nb))
			{
				//从最小的chunks中的第一个开始依次查找，若需求chunk的size大于查找到的chunk，则继续查找
				victim = victim->bk_nextsize;
				while (((unsigned long) (size = chunksize (victim)) <
					(unsigned long) (nb)))
					victim = victim->bk_nextsize;

				/* Avoid removing the first entry for a size so that the skip
					list does not have to be rerouted.	*/
				//*此处，已查找到size大于需求chunk size且最相近的chunk中的第一个
				//若相同大小的chunks不止这一个，则取相同大小的chunks中的第二个
				if (victim != last (bin)
					&& chunksize_nomask (victim)
					== chunksize_nomask (victim->fd))
					victim = victim->fd;

				//计算对此large chunk进行切割后剩余的部分的size
				remainder_size = size - nb;
				//若相同size的chunk不止一个,则由于此时victim不是相同大小chunks中的第一个，则:
				//有P->fd_nextsize == NULL,仅从fd/bk组成的双向循环链表中unlink出来
				//若相同size的chunk只有一个，则将victim从fd/bk链表及size链表中都unlink出来
				unlink (av, victim, bck, fwd);

				/* Exhaust */
				//如果切割后剩余部分小于chunk的最小size，则不进行切割，直接使用整个chunk
				if (remainder_size < MINSIZE)
				{
					set_inuse_bit_at_offset (victim, size);
					if (av != &main_arena)
					set_non_main_arena (victim);
				}
				/* Split */
				//若切割后剩余部分还能成为一个chunk，则切割
				else
				{
					//使用chunk的低地址部分作为需求chunk返回
					//chunk的高低址部分放入到unsorted bin的第一个位置上，并加入到unsorted bin链表
					remainder = chunk_at_offset (victim, nb);
					/* We cannot assume the unsorted list is empty and therefore
						have to perform a complete insert here.	*/
					bck = unsorted_chunks (av);
					fwd = bck->fd;
					if (__glibc_unlikely (fwd->bk != bck))
						malloc_printerr ("malloc(): corrupted unsorted chunks");
					remainder->bk = bck;
					remainder->fd = fwd;
					bck->fd = remainder;
					fwd->bk = remainder;
					//若remainder属于large chunk的范围内，由于unsorted bin不使用size指针，故将其置零
					if (!in_smallbin_range (remainder_size))
					{
						remainder->fd_nextsize = NULL;
						remainder->bk_nextsize = NULL;
					}
					//对切割后将要返回的chunk设置头
					//同时设置remainder的头部和尾部，由于其低地址处的chunk在使用，置prev_inuse位
					set_head (victim, nb | PREV_INUSE |
						(av != &main_arena ? NON_MAIN_ARENA : 0));
					set_head (remainder, remainder_size | PREV_INUSE);
					set_foot (remainder, remainder_size);
				}
				//检测，转换指针并返回
				check_malloced_chunk (av, victim, nb);
				void *p = chunk2mem (victim);
				alloc_perturb (p, bytes);
				return p;
			}
		}

		/*
			Search for a chunk by scanning bins, starting with next largest
			bin. This search is strictly by best-fit; i.e., the smallest
			(with ties going to approximately the least recently used) chunk
			that fits is selected.

			The bitmap avoids needing to check that most blocks are nonempty.
			The particular case of skipping all bins during warm-up phases
			when no chunks have been returned yet is faster than it might look.
		*/
		//*此处：
		//*若需求的是large chunk，则说明对应的large bin中无chunk或不足以满足需求chunk的size
		//*若需求的是small chunk，则说明对应的small bin中无chunk可分配
		//*因此查找比当前计算出的bin idx大的bin中是否存在符合条件的chunk
		++idx;
		bin = bin_at (av, idx);
		//计算当前bin index在binmap中对应的位置，以快速判断某个bin中是否存在chunks
		block = idx2block (idx);
		map = av->binmap[block];
		bit = idx2bit (idx);

		for (;; )
		{
			/* Skip rest of block if there are no more set bits in this block.	*/
			//若当前block(32个bit的bit组合)对应的bin中index比idx大的所有bins中都无chunks
			//或者index不合法(1U << ((i) & 0b11111))，
			//则说明此block不可用，查找binmap中后方的blocks
			if (bit > map || bit == 0)
			{
				//循环查找可用的block(后方block中至少一个bin中存在至少一个chunk)
				do
				{
					//若后方所有block中均无可用的chunks，则跳转到use_top,使用top chunk
					if (++block >= BINMAPSIZE) /* out of bins */
						goto use_top;
				} while ((map = av->binmap[block]) == 0);
				//若找到其中存在chunks的block，将需求bin的指针先设置在此block中的第一个bin处
				bin = bin_at (av, (block << BINMAPSHIFT));
				//设置bit标志，标明当前查找的bin在block中的位置
				bit = 1;
			}

			/* Advance to bin with set bit. There must be one. */
			//*从binmap保存的数据看来此block中存在需要的chunk
			//通过对bit标志移位后和map取并来判断bit标志对应的bin中是否有chunk
			//若没有则继续查找此block中的下一个bin
			while ((bit & map) == 0)
			{
				//获取下一个bin的表头
				bin = next_bin (bin);
				bit = bit << 1;
				assert (bit != 0);
			}

			/* Inspect the bin. It is likely to be non-empty */
			//*从binmap保存的数据看来此bin中存在需要的chunk
			//取该bin中的最后一个chunk(若为large bin，则是此bin中最小的chunk)
			victim = last (bin);

			//*若此bin中无chunks，则清除binmap对应bin的bit，并移位bit指向下一个bin,并从循环的开始重新执行
			if (victim == bin)
			{
				av->binmap[block] = map &= ~bit; /* Write through */
				bin = next_bin (bin);
				bit <<= 1;
			}
			//*若此bin中的确有chunks，则计算size，并计算保留或切割chunk
			else
			{
				size = chunksize (victim);
				assert ((unsigned long) (size) >= (unsigned long) (nb));

				remainder_size = size - nb;
				unlink (av, victim, bck, fwd);

				//在剩下部分小于chunk最小大小时保留chunk 
				if (remainder_size < MINSIZE)
				{
					set_inuse_bit_at_offset (victim, size);
					if (av != &main_arena)
					set_non_main_arena (victim);
				}
				//在剩下部分大小大于chunk最小大小时候切割chunk，被切割后剩下的部分称为last_remained
				else
				{
					remainder = chunk_at_offset (victim, nb);

					bck = unsorted_chunks (av);
					fwd = bck->fd;
					if (__glibc_unlikely (fwd->bk != bck))
						malloc_printerr ("malloc(): corrupted unsorted chunks 2");
					remainder->bk = bck;
					remainder->fd = fwd;
					bck->fd = remainder;
					fwd->bk = remainder;

					//last remained为:
						//*在无法满足最优分配原则的情况下，找到的大于需求chunk的最小chunk
						//*对这个chunk进行切割，满足需求chunk分配后剩下的部分
						//*last remainder会被放入unsorted bin中
					if (in_smallbin_range (nb))
						av->last_remainder = remainder;
					if (!in_smallbin_range (remainder_size))
					{
						remainder->fd_nextsize = NULL;
						remainder->bk_nextsize = NULL;
					}
					set_head (victim, nb | PREV_INUSE |
						(av != &main_arena ? NON_MAIN_ARENA : 0));
					set_head (remainder, remainder_size | PREV_INUSE);
					set_foot (remainder, remainder_size);
				}
				check_malloced_chunk (av, victim, nb);
				void *p = chunk2mem (victim);
				alloc_perturb (p, bytes);
				return p;
			}
		}

	//*此处，说明在经过了fastbin chunk合并，unsorted bin整理后，再进行的所有bins搜索中均没有size大于或等于需求的chunk size的chunk
	//*说明此时ptmalloc管理的所有数据结构中没有可直接使用的chunk
	//*此时，便通过切割top chunk的方式来对其进行分配
	use_top:
		/*
			If large enough, split off the chunk bordering the end of memory
			(held in av->top). Note that this is in accord with the best-fit
			search rule.	In effect, av->top is treated as larger (and thus
			less well fitting) than any other available chunk since it can
			be extended to be as large as necessary (up to system
			limitations).

			We require that av->top always exists (i.e., has size >=
			MINSIZE) after initialization, so if it would otherwise be
			exhausted by current request, it is replenished. (The main
			reason for ensuring it exists is that we may need MINSIZE space
			to put in fenceposts in sysmalloc.)
		*/

		victim = av->top;
		size = chunksize (victim);
		//检测top chunk size是否大于该arena从系统获得的size(说明top chunk size被人为更改)
		if (__glibc_unlikely (size > av->system_mem))
			malloc_printerr ("malloc(): corrupted top size");
		//top chunk size符合分配需求chunk的size需求，并且可以通过切割将top chunk一分为二
		if ((unsigned long) (size) >= (unsigned long) (nb + MINSIZE))
		{
			//切割后的高低址部分变为新的top chunk，低地址部分通过指针变换后返回给用户
			remainder_size = size - nb;
			remainder = chunk_at_offset (victim, nb);
			av->top = remainder;
			set_head (victim, nb | PREV_INUSE |
								(av != &main_arena ? NON_MAIN_ARENA : 0));
			set_head (remainder, remainder_size | PREV_INUSE);
			check_malloced_chunk (av, victim, nb);
			void *p = chunk2mem (victim);
			alloc_perturb (p, bytes);
			return p;
		}
		/* When we are using atomic ops to free fast chunks we can get
			here for all block sizes.	*/
		//若top chunk size无法满足chunk的size需求
		//检测arena 中是否存在fast chunk，若存在，则再次执行malloc_consolidate宏，并重新获得chunk对应的index
		//随后重新回到大循环开始处，并重新开始unsorted bin整理流程
		else if (atomic_load_relaxed (&av->have_fastchunks))
		{
			malloc_consolidate (av);
			/* restore original bin index */
			if (in_smallbin_range (nb))
				idx = smallbin_index (nb);
			else
				idx = largebin_index (nb);
		}
		/*
			Otherwise, relay to handle system-dependent cases
		*/
		//若top chunk无法满足分配需求，且此时也没有fast bin chunk，则通过系统
		else
		{
			void *p = sysmalloc (nb, av);
			if (p != NULL)
				alloc_perturb (p, bytes);
			return p;
		}
	}
}

/*
	------------------------------ free ------------------------------
 */

static void
_int_free (mstate av, mchunkptr p, int have_lock)
{
	INTERNAL_SIZE_T size;				/* its size */
	mfastbinptr *fb;						/* associated fastbin */
	mchunkptr nextchunk;				/* next contiguous chunk */
	INTERNAL_SIZE_T nextsize;		/* its size */
	int nextinuse;							/* true if nextchunk is used */
	INTERNAL_SIZE_T prevsize;		/* size of previous contiguous chunk */
	mchunkptr bck;							/* misc temp for linking */
	mchunkptr fwd;							/* misc temp for linking */

	size = chunksize (p);

	/* Little security check which won't hurt performance: the
		allocator never wrapps around at the end of the address space.
		Therefore we can exclude some size values which might appear
		here by accident or by "design" from some intruder.	*/
	//!检测chunk的size大小是否合适
	if (__builtin_expect ((uintptr_t) p > (uintptr_t) -size, 0)
			|| __builtin_expect (misaligned_chunk (p), 0))
		malloc_printerr ("free(): invalid pointer");
	/* We know that each chunk is at least MINSIZE bytes in size or a
		multiple of MALLOC_ALIGNMENT.	*/
	if (__glibc_unlikely (size < MINSIZE || !aligned_OK (size)))
		malloc_printerr ("free(): invalid size");

	check_inuse_chunk(av, p);

//*tcache回收流程
//若chunk size位于tcache范围内，则检测对应tcache chunk数量是否达到上限，若未，则放入
#if USE_TCACHE
	{
		size_t tc_idx = csize2tidx (size);

		if (tcache && tc_idx < mp_.tcache_bins
			&& tcache->counts[tc_idx] < mp_.tcache_count)
		{
			tcache_put (p, tc_idx);
			return;
		}
	}
#endif

	/*
		If eligible, place chunk on a fastbin so it can be found
		and used quickly in malloc.
	*/
//*fastbin chunk回收流程
	//chunk size在fastbin chunks内，则直接回收进入fastbin
	//若启动了ptmalloc空间动态收缩，则不将与top chunk相邻的fastbin chunk放入fastbin中
	if ((unsigned long)(size) <= (unsigned long)(get_max_fast ())
		#if TRIM_FASTBINS
			/*
			If TRIM_FASTBINS set, don't place chunks
			bordering top into fastbins
			*/
			&& (chunk_at_offset(p, size) != av->top)
		#endif
	)
	{
		//!检测chunk size的上下限
		//若异常，则记录错误，退出
		if (__builtin_expect (chunksize_nomask (chunk_at_offset (p, size))
				<= 2 * SIZE_SZ, 0)
				|| __builtin_expect (chunksize (chunk_at_offset (p, size))
				>= av->system_mem, 0))
		{
			bool fail = true;
			/* We might not have a lock at this point and concurrent modifications
				of system_mem might result in a false positive.	Redo the test after
				getting the lock.	*/
			if (!have_lock)
			{
				__libc_lock_lock (av->mutex);
				fail = (chunksize_nomask (chunk_at_offset (p, size)) <= 2 * SIZE_SZ
					|| chunksize (chunk_at_offset (p, size)) >= av->system_mem);
				__libc_lock_unlock (av->mutex);
			}

			if (fail)
				malloc_printerr ("free(): invalid next size (fast)");
		}

		free_perturb (chunk2mem(p), size - 2 * SIZE_SZ);
		//设置arena管理结构体malloc_state中的have_fastchunks域
		atomic_store_relaxed (&av->have_fastchunks, true);
		//获取对应的fastbin index及其fastbin表头
		unsigned int idx = fastbin_index(size);
		fb = &fastbin (av, idx);

		//old为对应fastbin中第一个chunk
		mchunkptr old = *fb, old2;

		//单线程
		//检测fastbin中第一个chunk是否为当前放入的chunk，若是则触发double free报错
		//正常则直接放入fastbin
		if (SINGLE_THREAD_P)
		{
			if (__builtin_expect (old == p, 0))
				malloc_printerr ("double free or corruption (fasttop)");
			p->fd = old;
			*fb = p;
		}
		else
		//多线程情况，使用原子操作将fastbinsY数组中对应fastbin表头更改为放入的chunk
		do
		{
			if (__builtin_expect (old == p, 0))
				malloc_printerr ("double free or corruption (fasttop)");
			p->fd = old2 = old;
		} while ((old = catomic_compare_and_exchange_val_rel (fb, p, old2)) != old2);

		/* Check that size of fastbin chunk at the top is the same as
			size of the chunk that we are adding.	We can dereference OLD
			only if we have the lock, otherwise it might have already been
			allocated again.	*/
		if (have_lock && old != NULL
			&& __builtin_expect (fastbin_index (chunksize (old)) != idx, 0))
			malloc_printerr ("invalid fastbin entry (free)");
	}

//*small bin / large bin情况
	else if (!chunk_is_mmapped(p))
	{
		//单线程则不必加锁，将have_lock设置为true
		if (SINGLE_THREAD_P)
			have_lock = true;

		if (!have_lock)
			__libc_lock_lock (av->mutex);
		//获取与被free的chunk地址上相邻的下一个chunk的地址
		nextchunk = chunk_at_offset(p, size);

		//!检测被free的chunk的空间是否指向此arena的top chunk
		if (__glibc_unlikely (p == av->top))
			malloc_printerr ("double free or corruption (top)");
		//!检测被free的chunk是否超出arena边界(在arena空间连续的前提下)
		if (__builtin_expect (contiguous (av)
				&& (char *) nextchunk
				>= ((char *) av->top + chunksize(av->top)), 0))
			malloc_printerr ("double free or corruption (out)");
		//!检测被free的chunk是否处于inuse状态
		if (__glibc_unlikely (!prev_inuse(nextchunk)))
			malloc_printerr ("double free or corruption (!prev)");

		nextsize = chunksize(nextchunk);
		//!检测地址上相邻的下一个chunk的大小是否合法(是否被人为修改)
		if (__builtin_expect (chunksize_nomask (nextchunk) <= 2 * SIZE_SZ, 0)
			|| __builtin_expect (nextsize >= av->system_mem, 0))
			malloc_printerr ("free(): invalid next size (normal)");
		//!若设置了perturb_byte，则使用perturb_byte字符填充chunk
		free_perturb (chunk2mem(p), size - 2 * SIZE_SZ);

		//*由于每个进入unsorted bin的chunk都需要进行前后向合并，在每一个chunk被free的时候，其前后最多出现各一个相邻的free chunk
		//*于是仅需要分别进行一次前后向检测并在可合并时合并即可
	//*前向合并
		//若相邻地址前一个chunk空闲，则将其从bin中unlink出来，并改变size大小
		if (!prev_inuse(p))
		{
			prevsize = prev_size (p);
			size += prevsize;
			p = chunk_at_offset(p, -((long) prevsize));
			if (__glibc_unlikely (chunksize(p) != prevsize))
				malloc_printerr ("corrupted size vs. prev_size while consolidating");
			unlink(av, p, bck, fwd);
		}
		//若下个chunk不为top chunk
		if (nextchunk != av->top)
		{
			//获取位于下下个chunk中的prev_inuse位，得到下个chunk是否inuse的信息
			nextinuse = inuse_bit_at_offset(nextchunk, nextsize);

			//后向合并
			//将后方一个chunk从bin中unlink出来并调整size
			if (!nextinuse) 
			{
				unlink(av, nextchunk, bck, fwd);
				size += nextsize;
			}
			//若无法后向合并，则清理后方chunk的inuse位
			else
				clear_inuse_bit_at_offset(nextchunk, 0);

			/*
			Place the chunk in unsorted chunk list. Chunks are
			not placed into regular bins until after they have
			been given one chance to be used in malloc.
			*/

			//将合并后的chunk放入到unsorted bin中
			//!检测unsorted bin表头和第一个chunk的双向链表
			bck = unsorted_chunks(av);
			fwd = bck->fd;
			if (__glibc_unlikely (fwd->bk != bck))
				malloc_printerr ("free(): corrupted unsorted chunks");
			//将free的chunk放在unsorted bin中的第一个位置
			p->fd = fwd;
			p->bk = bck;
			//unsorted bin中不使用large bin chunk的size指针域
			if (!in_smallbin_range(size))
			{
				p->fd_nextsize = NULL;
				p->bk_nextsize = NULL;
			}
			bck->fd = p;
			fwd->bk = p;
			//前方chunk必为inuse状态(或为不清除inuse bit的chunk)，不然已经合并
			set_head(p, size | PREV_INUSE);
			set_foot(p, size);
			check_free_chunk(av, p);
		}

		//p指向的chunk和top chunk相邻，则直接合并，并修改top chunk指针
		else
		{
			size += nextsize;
			set_head(p, size | PREV_INUSE);
			av->top = p;
			check_chunk(av, p);
		}

		/*
			If freeing a large space, consolidate possibly-surrounding
			chunks. Then, if the total unused topmost memory exceeds trim
			threshold, ask malloc_trim to reduce top.

			Unless max_fast is 0, we don't know if there are fastbins
			bordering top, so we cannot tell for sure whether threshold
			has been reached unless fastbins are consolidated.	But we
			don't want to consolidate on each free.	As a compromise,
			consolidation is performed if FASTBIN_CONSOLIDATION_THRESHOLD
			is reached.
		*/
		//若当前chunk(合并后chunk)的大小大于fastbin合并阈值，且设置了have_fastchunks宏，则触发consolidate
		if ((unsigned long)(size) >= FASTBIN_CONSOLIDATION_THRESHOLD)
		{
			if (atomic_load_relaxed (&av->have_fastchunks))
				malloc_consolidate(av);
			//若空间位于main arena中，且top chunk大于heap收缩阈值，则使用systrim函数收缩main arena空间
			if (av == &main_arena) 
			{
			#ifndef MORECORE_CANNOT_TRIM
				if ((unsigned long)(chunksize(av->top)) >=
						(unsigned long)(mp_.trim_threshold))
					systrim(mp_.top_pad, av);
			#endif
			}
			//若为thread arena，则获取当前top chunk所在的sub heap的头指针，并尝试收缩
			else
			{
				/* Always try heap_trim(), even if the top chunk is not
					large, because the corresponding heap might go away.	*/
				heap_info *heap = heap_for_ptr(top(av));

				assert(heap->ar_ptr == av);
				heap_trim(heap, mp_.top_pad);
			}
		}
		if (!have_lock)
			__libc_lock_unlock (av->mutex);
	}
	//若该chunk为mmaped chunk，则使用munmap释放
	else {
		munmap_chunk (p);
	}
}

/*
	------------------------- malloc_consolidate -------------------------

	malloc_consolidate is a specialized version of free() that tears
	down chunks held in fastbins.	Free itself cannot be used for this
	purpose since, among other things, it might place chunks back onto
	fastbins.	So, instead, we need to use a minor variant of the same
	code.
*/

static void malloc_consolidate(mstate av)
{
	mfastbinptr 	*fb;							/* current fastbin being consolidated */
	mchunkptr		p;								/* current chunk being consolidated */
	mchunkptr		nextp;							/* next chunk to consolidate */
	mchunkptr		unsorted_bin;					/* bin header */
	mchunkptr		first_unsorted;					/* chunk to link to */

	/* These have same use as in free() */
	mchunkptr		nextchunk;
	INTERNAL_SIZE_T size;
	INTERNAL_SIZE_T nextsize;
	INTERNAL_SIZE_T prevsize;
	int				nextinuse;
	mchunkptr		bck;
	mchunkptr		fwd;

	atomic_store_relaxed (&av->have_fastchunks, false);
	//bin[1]为unsorted bin，获取unsorted bin表头chunk指针，仅可使用fd和bk指针字段，分别为bins[0],bins[1]
	unsorted_bin = unsorted_chunks(av);

	/*
		Remove each chunk from fast bin and consolidate it, placing it
		then in unsorted bin. Among other reasons for doing this,
		placing in unsorted bin avoids needing to calculate actual bins
		until malloc is sure that chunks aren't immediately going to be
		reused anyway.
	*/

	maxfb = &fastbin (av, NFASTBINS - 1);
	fb = &fastbin (av, 0);		//获取第一个fastbin
	//不同fastbin的循环遍历
	do {
		p = atomic_exchange_acq (fb, NULL);
		if (p != 0) {
			//同一个fastbin中的fast chunk遍历循环
			do {
				//检查获取到的fast chunk大小是否和对应的fastbin相符
				{
					unsigned int idx = fastbin_index (chunksize (p));
					if ((&fastbin (av, idx)) != fb)
						malloc_printerr ("malloc_consolidate(): invalid chunk size");
				}
				//永远将fd指向非inuse状态相邻chunks的第一个chunk
				check_inuse_chunk(av, p);				//检测该chunk的inuse状态和前后chunk的状态与属性的对应正确性
				nextp = p->fd;							//保存bin中后一个chunk的指针
				/* Slightly streamlined version of consolidation code in free() */
				size = chunksize (p);
				nextchunk = chunk_at_offset(p, size);
				nextsize = chunksize(nextchunk);		//获取地址相邻的下一个chunk的属性

			//检测前后chunk的使用状态，若没有处于使用状态，则将其脱离出对应的bin中
				if (!prev_inuse(p)) {					//若前一chunk未使用
					prevsize = prev_size (p);
					size += prevsize;					//计算合成后的chunk大小
					p = chunk_at_offset(p, -((long) prevsize));		//让p指向前一个chunk
					if (__glibc_unlikely (chunksize(p) != prevsize))
						malloc_printerr ("corrupted size vs. prev_size in fastbins");	//! size / prev_size更改检测(仅在chunk合并时作用)
					unlink(av, p, bck, fwd);						//将p的前一个chunk从双向链表上脱离(chunk类型未知)
				}
				//若下一个chunk不为top chunk
				if (nextchunk != av->top) {
					nextinuse = inuse_bit_at_offset(nextchunk, nextsize);
					if (!nextinuse) {								//若下一个chunk未在使用
						size += nextsize;
						unlink(av, nextchunk, bck, fwd);			//将p的下一个chunk从bin中脱离(chunk类型未知)
					} 
					else
						clear_inuse_bit_at_offset(nextchunk, 0);	//清除原始p指向的fast chunk的inuse状态(位于下一个chunk的size中的prev_inuse位)

					first_unsorted = unsorted_bin->fd;					//获取第一个unsorted chunk指针
					unsorted_bin->fd = p;								//将合并后的chunk，放入到unsorted bin的头部
					first_unsorted->bk = p;								//处理好双向链表

					if (!in_smallbin_range (size)) {					//处于large chunk的大小范围
						p->fd_nextsize = NULL;							//将size指针字段置零
						p->bk_nextsize = NULL;
					}
					set_head(p, size | PREV_INUSE);						//设置新chunk的size，并且将prev_inuse位设置为1(由于前一个chunk为inuse状态)
					p->bk = unsorted_bin;								//将p的前后相关指针设置为unsorted bin中的对应指针
					p->fd = first_unsorted;
					set_foot(p, size);									//设置地址相邻后方的chunk的prev_size为新的size大小
				}
				//若是top chunk
				else {
					size += nextsize;									//合并top chunk和此chunk
					set_head(p, size | PREV_INUSE);
					av->top = p;										//重新设置top chunk指针
				}
			} while ( (p = nextp) != 0);								//对fastbin中的下一个chunk进行同样的工作
		}
	} while (fb++ != maxfb);
}

/*
	------------------------------ realloc ------------------------------
*/

void*
_int_realloc(mstate av, mchunkptr oldp, INTERNAL_SIZE_T oldsize,
			INTERNAL_SIZE_T nb)
{
	mchunkptr				newp;						/* chunk to return */
	INTERNAL_SIZE_T	newsize;				/* its size */
	void*					newmem;					/* corresponding user mem */

	mchunkptr				next;						/* next contiguous chunk after oldp */

	mchunkptr				remainder;			/* extra space at end of newp */
	unsigned long		remainder_size;	/* its size */

	mchunkptr				bck;						/* misc temp for linking */
	mchunkptr				fwd;						/* misc temp for linking */

	unsigned long		copysize;				/* bytes to copy */
	unsigned int		ncopies;				/* INTERNAL_SIZE_T words to copy */
	INTERNAL_SIZE_T* s;							/* copy source */
	INTERNAL_SIZE_T* d;							/* copy destination */

	/* oldmem size */
	if (__builtin_expect (chunksize_nomask (oldp) <= 2 * SIZE_SZ, 0)
			|| __builtin_expect (oldsize >= av->system_mem, 0))
		malloc_printerr ("realloc(): invalid old size");

	check_inuse_chunk (av, oldp);

	/* All callers already filter out mmap'ed chunks.	*/
	assert (!chunk_is_mmapped (oldp));

	next = chunk_at_offset (oldp, oldsize);
	INTERNAL_SIZE_T nextsize = chunksize (next);
	if (__builtin_expect (chunksize_nomask (next) <= 2 * SIZE_SZ, 0)
			|| __builtin_expect (nextsize >= av->system_mem, 0))
		malloc_printerr ("realloc(): invalid next size");

	if ((unsigned long) (oldsize) >= (unsigned long) (nb))
		{
			/* already big enough; split below */
			newp = oldp;
			newsize = oldsize;
		}

	else
		{
			/* Try to expand forward into top */
			if (next == av->top &&
					(unsigned long) (newsize = oldsize + nextsize) >=
					(unsigned long) (nb + MINSIZE))
				{
					set_head_size (oldp, nb | (av != &main_arena ? NON_MAIN_ARENA : 0));
					av->top = chunk_at_offset (oldp, nb);
					set_head (av->top, (newsize - nb) | PREV_INUSE);
					check_inuse_chunk (av, oldp);
					return chunk2mem (oldp);
				}

			/* Try to expand forward into next chunk;	split off remainder below */
			else if (next != av->top &&
							!inuse (next) &&
							(unsigned long) (newsize = oldsize + nextsize) >=
							(unsigned long) (nb))
			{
				newp = oldp;
				unlink (av, next, bck, fwd);
			}

			/* allocate, copy, free */
			else
			{
				newmem = _int_malloc (av, nb - MALLOC_ALIGN_MASK);
				if (newmem == 0)
					return 0; /* propagate failure */

				newp = mem2chunk (newmem);
				newsize = chunksize (newp);

				/*
					Avoid copy if newp is next chunk after oldp.
				*/
				if (newp == next)
					{
						newsize += oldsize;
						newp = oldp;
					}
				else
					{
						/*
							Unroll copy of <= 36 bytes (72 if 8byte sizes)
							We know that contents have an odd number of
							INTERNAL_SIZE_T-sized words; minimally 3.
						*/

						copysize = oldsize - SIZE_SZ;
						s = (INTERNAL_SIZE_T *) (chunk2mem (oldp));
						d = (INTERNAL_SIZE_T *) (newmem);
						ncopies = copysize / sizeof (INTERNAL_SIZE_T);
						assert (ncopies >= 3);

						if (ncopies > 9)
							memcpy (d, s, copysize);

						else
							{
								*(d + 0) = *(s + 0);
								*(d + 1) = *(s + 1);
								*(d + 2) = *(s + 2);
								if (ncopies > 4)
									{
										*(d + 3) = *(s + 3);
										*(d + 4) = *(s + 4);
										if (ncopies > 6)
											{
												*(d + 5) = *(s + 5);
												*(d + 6) = *(s + 6);
												if (ncopies > 8)
													{
														*(d + 7) = *(s + 7);
														*(d + 8) = *(s + 8);
													}
											}
									}
							}

						_int_free (av, oldp, 1);
						check_inuse_chunk (av, newp);
						return chunk2mem (newp);
					}
				}
		}

	/* If possible, free extra space in old or extended chunk */

	assert ((unsigned long) (newsize) >= (unsigned long) (nb));

	remainder_size = newsize - nb;

	if (remainder_size < MINSIZE)	/* not enough extra to split off */
		{
			set_head_size (newp, newsize | (av != &main_arena ? NON_MAIN_ARENA : 0));
			set_inuse_bit_at_offset (newp, newsize);
		}
	else	/* split remainder */
		{
			remainder = chunk_at_offset (newp, nb);
			set_head_size (newp, nb | (av != &main_arena ? NON_MAIN_ARENA : 0));
			set_head (remainder, remainder_size | PREV_INUSE |
								(av != &main_arena ? NON_MAIN_ARENA : 0));
			/* Mark remainder as inuse so free() won't complain */
			set_inuse_bit_at_offset (remainder, remainder_size);
			_int_free (av, remainder, 1);
		}

	check_inuse_chunk (av, newp);
	return chunk2mem (newp);
}

/*
	------------------------------ memalign ------------------------------
 */

static void *
_int_memalign (mstate av, size_t alignment, size_t bytes)
{
	INTERNAL_SIZE_T nb;						/* padded	request size */
	char *m;												/* memory returned by malloc call */
	mchunkptr p;										/* corresponding chunk */
	char *brk;											/* alignment point within p */
	mchunkptr newp;								/* chunk to return */
	INTERNAL_SIZE_T newsize;				/* its size */
	INTERNAL_SIZE_T leadsize;			/* leading space before alignment point */
	mchunkptr remainder;						/* spare room at end to split off */
	unsigned long remainder_size;	/* its size */
	INTERNAL_SIZE_T size;



	checked_request2size (bytes, nb);

	/*
		Strategy: find a spot within that chunk that meets the alignment
		request, and then possibly free the leading and trailing space.
	*/


	/* Check for overflow.	*/
	if (nb > SIZE_MAX - alignment - MINSIZE)
		{
			__set_errno (ENOMEM);
			return 0;
		}

	/* Call malloc with worst case padding to hit alignment. */

	m = (char *) (_int_malloc (av, nb + alignment + MINSIZE));

	if (m == 0)
		return 0;					/* propagate failure */

	p = mem2chunk (m);

	if ((((unsigned long) (m)) % alignment) != 0)	/* misaligned */

		{ /*
								Find an aligned spot inside chunk.	Since we need to give back
								leading space in a chunk of at least MINSIZE, if the first
								calculation places us at a spot with less than MINSIZE leader,
								we can move to the next aligned spot -- we've allocated enough
								total room so that this is always possible.
								*/
			brk = (char *) mem2chunk (((unsigned long) (m + alignment - 1)) &
																- ((signed long) alignment));
			if ((unsigned long) (brk - (char *) (p)) < MINSIZE)
				brk += alignment;

			newp = (mchunkptr) brk;
			leadsize = brk - (char *) (p);
			newsize = chunksize (p) - leadsize;

			/* For mmapped chunks, just adjust offset */
			if (chunk_is_mmapped (p))
				{
					set_prev_size (newp, prev_size (p) + leadsize);
					set_head (newp, newsize | IS_MMAPPED);
					return chunk2mem (newp);
				}

			/* Otherwise, give back leader, use the rest */
			set_head (newp, newsize | PREV_INUSE |
								(av != &main_arena ? NON_MAIN_ARENA : 0));
			set_inuse_bit_at_offset (newp, newsize);
			set_head_size (p, leadsize | (av != &main_arena ? NON_MAIN_ARENA : 0));
			_int_free (av, p, 1);
			p = newp;

			assert (newsize >= nb &&
							(((unsigned long) (chunk2mem (p))) % alignment) == 0);
		}

	/* Also give back spare room at the end */
	if (!chunk_is_mmapped (p))
		{
			size = chunksize (p);
			if ((unsigned long) (size) > (unsigned long) (nb + MINSIZE))
				{
					remainder_size = size - nb;
					remainder = chunk_at_offset (p, nb);
					set_head (remainder, remainder_size | PREV_INUSE |
										(av != &main_arena ? NON_MAIN_ARENA : 0));
					set_head_size (p, nb);
					_int_free (av, remainder, 1);
				}
		}

	check_inuse_chunk (av, p);
	return chunk2mem (p);
}


/*
	------------------------------ malloc_trim ------------------------------
 */

static int
mtrim (mstate av, size_t pad)
{
	/* Ensure all blocks are consolidated.	*/
	malloc_consolidate (av);

	const size_t ps = GLRO (dl_pagesize);
	int psindex = bin_index (ps);
	const size_t psm1 = ps - 1;

	int result = 0;
	for (int i = 1; i < NBINS; ++i)
		if (i == 1 || i >= psindex)
			{
				mbinptr bin = bin_at (av, i);

				for (mchunkptr p = last (bin); p != bin; p = p->bk)
					{
						INTERNAL_SIZE_T size = chunksize (p);

						if (size > psm1 + sizeof (struct malloc_chunk))
							{
								/* See whether the chunk contains at least one unused page.	*/
								char *paligned_mem = (char *) (((uintptr_t) p
																								+ sizeof (struct malloc_chunk)
																								+ psm1) & ~psm1);

								assert ((char *) chunk2mem (p) + 4 * SIZE_SZ <= paligned_mem);
								assert ((char *) p + size > paligned_mem);

								/* This is the size we could potentially free.	*/
								size -= paligned_mem - (char *) p;

								if (size > psm1)
									{
#if MALLOC_DEBUG
										/* When debugging we simulate destroying the memory
											content.	*/
										memset (paligned_mem, 0x89, size & ~psm1);
#endif
										__madvise (paligned_mem, size & ~psm1, MADV_DONTNEED);

										result = 1;
									}
							}
					}
			}

#ifndef MORECORE_CANNOT_TRIM
	return result | (av == &main_arena ? systrim (pad, av) : 0);

#else
	return result;
#endif
}


int
__malloc_trim (size_t s)
{
	int result = 0;

	if (__malloc_initialized < 0)
		ptmalloc_init ();

	mstate ar_ptr = &main_arena;
	do
		{
			__libc_lock_lock (ar_ptr->mutex);
			result |= mtrim (ar_ptr, s);
			__libc_lock_unlock (ar_ptr->mutex);

			ar_ptr = ar_ptr->next;
		}
	while (ar_ptr != &main_arena);

	return result;
}


/*
	------------------------- malloc_usable_size -------------------------
 */

static size_t
musable (void *mem)
{
	mchunkptr p;
	if (mem != 0)
		{
			p = mem2chunk (mem);

			if (__builtin_expect (using_malloc_checking == 1, 0))
				return malloc_check_get_size (p);

			if (chunk_is_mmapped (p))
	{
		if (DUMPED_MAIN_ARENA_CHUNK (p))
			return chunksize (p) - SIZE_SZ;
		else
			return chunksize (p) - 2 * SIZE_SZ;
	}
			else if (inuse (p))
				return chunksize (p) - SIZE_SZ;
		}
	return 0;
}


size_t
__malloc_usable_size (void *m)
{
	size_t result;

	result = musable (m);
	return result;
}

/*
	------------------------------ mallinfo ------------------------------
	Accumulate malloc statistics for arena AV into M.
 */

static void
int_mallinfo (mstate av, struct mallinfo *m)
{
	size_t i;
	mbinptr b;
	mchunkptr p;
	INTERNAL_SIZE_T avail;
	INTERNAL_SIZE_T fastavail;
	int nblocks;
	int nfastblocks;

	check_malloc_state (av);

	/* Account for top */
	avail = chunksize (av->top);
	nblocks = 1;	/* top always exists */

	/* traverse fastbins */
	nfastblocks = 0;
	fastavail = 0;

	for (i = 0; i < NFASTBINS; ++i)
		{
			for (p = fastbin (av, i); p != 0; p = p->fd)
				{
					++nfastblocks;
					fastavail += chunksize (p);
				}
		}

	avail += fastavail;

	/* traverse regular bins */
	for (i = 1; i < NBINS; ++i)
		{
			b = bin_at (av, i);
			for (p = last (b); p != b; p = p->bk)
				{
					++nblocks;
					avail += chunksize (p);
				}
		}

	m->smblks += nfastblocks;
	m->ordblks += nblocks;
	m->fordblks += avail;
	m->uordblks += av->system_mem - avail;
	m->arena += av->system_mem;
	m->fsmblks += fastavail;
	if (av == &main_arena)
		{
			m->hblks = mp_.n_mmaps;
			m->hblkhd = mp_.mmapped_mem;
			m->usmblks = 0;
			m->keepcost = chunksize (av->top);
		}
}


struct mallinfo
__libc_mallinfo (void)
{
	struct mallinfo m;
	mstate ar_ptr;

	if (__malloc_initialized < 0)
		ptmalloc_init ();

	memset (&m, 0, sizeof (m));
	ar_ptr = &main_arena;
	do
		{
			__libc_lock_lock (ar_ptr->mutex);
			int_mallinfo (ar_ptr, &m);
			__libc_lock_unlock (ar_ptr->mutex);

			ar_ptr = ar_ptr->next;
		}
	while (ar_ptr != &main_arena);

	return m;
}

/*
	------------------------------ malloc_stats ------------------------------
 */

void
__malloc_stats (void)
{
	int i;
	mstate ar_ptr;
	unsigned int in_use_b = mp_.mmapped_mem, system_b = in_use_b;

	if (__malloc_initialized < 0)
		ptmalloc_init ();
	_IO_flockfile (stderr);
	int old_flags2 = stderr->_flags2;
	stderr->_flags2 |= _IO_FLAGS2_NOTCANCEL;
	for (i = 0, ar_ptr = &main_arena;; i++)
		{
			struct mallinfo mi;

			memset (&mi, 0, sizeof (mi));
			__libc_lock_lock (ar_ptr->mutex);
			int_mallinfo (ar_ptr, &mi);
			fprintf (stderr, "Arena %d:\n", i);
			fprintf (stderr, "system bytes		= %10u\n", (unsigned int) mi.arena);
			fprintf (stderr, "in use bytes		= %10u\n", (unsigned int) mi.uordblks);
#if MALLOC_DEBUG > 1
			if (i > 0)
				dump_heap (heap_for_ptr (top (ar_ptr)));
#endif
			system_b += mi.arena;
			in_use_b += mi.uordblks;
			__libc_lock_unlock (ar_ptr->mutex);
			ar_ptr = ar_ptr->next;
			if (ar_ptr == &main_arena)
				break;
		}
	fprintf (stderr, "Total (incl. mmap):\n");
	fprintf (stderr, "system bytes		= %10u\n", system_b);
	fprintf (stderr, "in use bytes		= %10u\n", in_use_b);
	fprintf (stderr, "max mmap regions = %10u\n", (unsigned int) mp_.max_n_mmaps);
	fprintf (stderr, "max mmap bytes	= %10lu\n",
					(unsigned long) mp_.max_mmapped_mem);
	stderr->_flags2 = old_flags2;
	_IO_funlockfile (stderr);
}


/*
	------------------------------ mallopt ------------------------------
 */
static inline int
__always_inline
do_set_trim_threshold (size_t value)
{
	LIBC_PROBE (memory_mallopt_trim_threshold, 3, value, mp_.trim_threshold,
				mp_.no_dyn_threshold);
	mp_.trim_threshold = value;
	mp_.no_dyn_threshold = 1;
	return 1;
}

static inline int
__always_inline
do_set_top_pad (size_t value)
{
	LIBC_PROBE (memory_mallopt_top_pad, 3, value, mp_.top_pad,
				mp_.no_dyn_threshold);
	mp_.top_pad = value;
	mp_.no_dyn_threshold = 1;
	return 1;
}

static inline int
__always_inline
do_set_mmap_threshold (size_t value)
{
	/* Forbid setting the threshold too high.	*/
	if (value <= HEAP_MAX_SIZE / 2)
		{
			LIBC_PROBE (memory_mallopt_mmap_threshold, 3, value, mp_.mmap_threshold,
			mp_.no_dyn_threshold);
			mp_.mmap_threshold = value;
			mp_.no_dyn_threshold = 1;
			return 1;
		}
	return 0;
}

static inline int
__always_inline
do_set_mmaps_max (int32_t value)
{
	LIBC_PROBE (memory_mallopt_mmap_max, 3, value, mp_.n_mmaps_max,
				mp_.no_dyn_threshold);
	mp_.n_mmaps_max = value;
	mp_.no_dyn_threshold = 1;
	return 1;
}

static inline int
__always_inline
do_set_mallopt_check (int32_t value)
{
	return 1;
}

static inline int
__always_inline
do_set_perturb_byte (int32_t value)
{
	LIBC_PROBE (memory_mallopt_perturb, 2, value, perturb_byte);
	perturb_byte = value;
	return 1;
}

static inline int
__always_inline
do_set_arena_test (size_t value)
{
	LIBC_PROBE (memory_mallopt_arena_test, 2, value, mp_.arena_test);
	mp_.arena_test = value;
	return 1;
}

static inline int
__always_inline
do_set_arena_max (size_t value)
{
	LIBC_PROBE (memory_mallopt_arena_max, 2, value, mp_.arena_max);
	mp_.arena_max = value;
	return 1;
}

#if USE_TCACHE
static inline int
__always_inline
do_set_tcache_max (size_t value)
{
	if (value >= 0 && value <= MAX_TCACHE_SIZE)
		{
			LIBC_PROBE (memory_tunable_tcache_max_bytes, 2, value, mp_.tcache_max_bytes);
			mp_.tcache_max_bytes = value;
			mp_.tcache_bins = csize2tidx (request2size(value)) + 1;
		}
	return 1;
}

static inline int
__always_inline
do_set_tcache_count (size_t value)
{
	LIBC_PROBE (memory_tunable_tcache_count, 2, value, mp_.tcache_count);
	mp_.tcache_count = value;
	return 1;
}

static inline int
__always_inline
do_set_tcache_unsorted_limit (size_t value)
{
	LIBC_PROBE (memory_tunable_tcache_unsorted_limit, 2, value, mp_.tcache_unsorted_limit);
	mp_.tcache_unsorted_limit = value;
	return 1;
}
#endif

int
__libc_mallopt (int param_number, int value)
{
	mstate av = &main_arena;
	int res = 1;

	if (__malloc_initialized < 0)
		ptmalloc_init ();
	__libc_lock_lock (av->mutex);

	LIBC_PROBE (memory_mallopt, 2, param_number, value);

	/* We must consolidate main arena before changing max_fast
		(see definition of set_max_fast).	*/
	malloc_consolidate (av);

	switch (param_number)
		{
		case M_MXFAST:
			if (value >= 0 && value <= MAX_FAST_SIZE)
				{
					LIBC_PROBE (memory_mallopt_mxfast, 2, value, get_max_fast ());
					set_max_fast (value);
				}
			else
				res = 0;
			break;

		case M_TRIM_THRESHOLD:
			do_set_trim_threshold (value);
			break;

		case M_TOP_PAD:
			do_set_top_pad (value);
			break;

		case M_MMAP_THRESHOLD:
			res = do_set_mmap_threshold (value);
			break;

		case M_MMAP_MAX:
			do_set_mmaps_max (value);
			break;

		case M_CHECK_ACTION:
			do_set_mallopt_check (value);
			break;

		case M_PERTURB:
			do_set_perturb_byte (value);
			break;

		case M_ARENA_TEST:
			if (value > 0)
	do_set_arena_test (value);
			break;

		case M_ARENA_MAX:
			if (value > 0)
	do_set_arena_max (value);
			break;
		}
	__libc_lock_unlock (av->mutex);
	return res;
}
libc_hidden_def (__libc_mallopt)


/*
	-------------------- Alternative MORECORE functions --------------------
 */


/*
	General Requirements for MORECORE.

	The MORECORE function must have the following properties:

	If MORECORE_CONTIGUOUS is false:

 * MORECORE must allocate in multiples of pagesize. It will
			only be called with arguments that are multiples of pagesize.

 * MORECORE(0) must return an address that is at least
			MALLOC_ALIGNMENT aligned. (Page-aligning always suffices.)

	else (i.e. If MORECORE_CONTIGUOUS is true):

 * Consecutive calls to MORECORE with positive arguments
			return increasing addresses, indicating that space has been
			contiguously extended.

 * MORECORE need not allocate in multiples of pagesize.
			Calls to MORECORE need not have args of multiples of pagesize.

 * MORECORE need not page-align.

	In either case:

 * MORECORE may allocate more memory than requested. (Or even less,
			but this will generally result in a malloc failure.)

 * MORECORE must not allocate memory when given argument zero, but
			instead return one past the end address of memory from previous
			nonzero call. This malloc does NOT call MORECORE(0)
			until at least one call with positive arguments is made, so
			the initial value returned is not important.

 * Even though consecutive calls to MORECORE need not return contiguous
			addresses, it must be OK for malloc'ed chunks to span multiple
			regions in those cases where they do happen to be contiguous.

 * MORECORE need not handle negative arguments -- it may instead
			just return MORECORE_FAILURE when given negative arguments.
			Negative arguments are always multiples of pagesize. MORECORE
			must not misinterpret negative args as large positive unsigned
			args. You can suppress all such calls from even occurring by defining
			MORECORE_CANNOT_TRIM,

	There is some variation across systems about the type of the
	argument to sbrk/MORECORE. If size_t is unsigned, then it cannot
	actually be size_t, because sbrk supports negative args, so it is
	normally the signed type of the same width as size_t (sometimes
	declared as "intptr_t", and sometimes "ptrdiff_t").	It doesn't much
	matter though. Internally, we use "long" as arguments, which should
	work across all reasonable possibilities.

	Additionally, if MORECORE ever returns failure for a positive
	request, then mmap is used as a noncontiguous system allocator. This
	is a useful backup strategy for systems with holes in address spaces
	-- in this case sbrk cannot contiguously expand the heap, but mmap
	may be able to map noncontiguous space.

	If you'd like mmap to ALWAYS be used, you can define MORECORE to be
	a function that always returns MORECORE_FAILURE.

	If you are using this malloc with something other than sbrk (or its
	emulation) to supply memory regions, you probably want to set
	MORECORE_CONTIGUOUS as false.	As an example, here is a custom
	allocator kindly contributed for pre-OSX macOS.	It uses virtually
	but not necessarily physically contiguous non-paged memory (locked
	in, present and won't get swapped out).	You can use it by
	uncommenting this section, adding some #includes, and setting up the
	appropriate defines above:

 *#define MORECORE osMoreCore
 *#define MORECORE_CONTIGUOUS 0

	There is also a shutdown routine that should somehow be called for
	cleanup upon program exit.

 *#define MAX_POOL_ENTRIES 100
 *#define MINIMUM_MORECORE_SIZE	(64 * 1024)
	static int next_os_pool;
	void *our_os_pools[MAX_POOL_ENTRIES];

	void *osMoreCore(int size)
	{
		void *ptr = 0;
		static void *sbrk_top = 0;

		if (size > 0)
		{
			if (size < MINIMUM_MORECORE_SIZE)
				size = MINIMUM_MORECORE_SIZE;
			if (CurrentExecutionLevel() == kTaskLevel)
				ptr = PoolAllocateResident(size + RM_PAGE_SIZE, 0);
			if (ptr == 0)
			{
				return (void *) MORECORE_FAILURE;
			}
			// save ptrs so they can be freed during cleanup
			our_os_pools[next_os_pool] = ptr;
			next_os_pool++;
			ptr = (void *) ((((unsigned long) ptr) + RM_PAGE_MASK) & ~RM_PAGE_MASK);
			sbrk_top = (char *) ptr + size;
			return ptr;
		}
		else if (size < 0)
		{
			// we don't currently support shrink behavior
			return (void *) MORECORE_FAILURE;
		}
		else
		{
			return sbrk_top;
		}
	}

	// cleanup any allocated memory pools
	// called as last thing before shutting down driver

	void osCleanupMem(void)
	{
		void **ptr;

		for (ptr = our_os_pools; ptr < &our_os_pools[MAX_POOL_ENTRIES]; ptr++)
			if (*ptr)
			{
				PoolDeallocate(*ptr);
 * ptr = 0;
			}
	}

 */


/* Helper code.	*/

extern char **__libc_argv attribute_hidden;

static void
malloc_printerr (const char *str)
{
	__libc_message (do_abort, "%s\n", str);
	__builtin_unreachable ();
}

/* We need a wrapper function for one of the additions of POSIX.	*/
int
__posix_memalign (void **memptr, size_t alignment, size_t size)
{
	void *mem;

	/* Test whether the SIZE argument is valid.	It must be a power of
		two multiple of sizeof (void *).	*/
	if (alignment % sizeof (void *) != 0
			|| !powerof2 (alignment / sizeof (void *))
			|| alignment == 0)
		return EINVAL;


	void *address = RETURN_ADDRESS (0);
	mem = _mid_memalign (alignment, size, address);

	if (mem != NULL)
		{
			*memptr = mem;
			return 0;
		}

	return ENOMEM;
}
weak_alias (__posix_memalign, posix_memalign)


int
__malloc_info (int options, FILE *fp)
{
	/* For now, at least.	*/
	if (options != 0)
		return EINVAL;

	int n = 0;
	size_t total_nblocks = 0;
	size_t total_nfastblocks = 0;
	size_t total_avail = 0;
	size_t total_fastavail = 0;
	size_t total_system = 0;
	size_t total_max_system = 0;
	size_t total_aspace = 0;
	size_t total_aspace_mprotect = 0;



	if (__malloc_initialized < 0)
		ptmalloc_init ();

	fputs ("<malloc version=\"1\">\n", fp);

	/* Iterate over all arenas currently in use.	*/
	mstate ar_ptr = &main_arena;
	do
		{
			fprintf (fp, "<heap nr=\"%d\">\n<sizes>\n", n++);

			size_t nblocks = 0;
			size_t nfastblocks = 0;
			size_t avail = 0;
			size_t fastavail = 0;
			struct
			{
	size_t from;
	size_t to;
	size_t total;
	size_t count;
			} sizes[NFASTBINS + NBINS - 1];
#define nsizes (sizeof (sizes) / sizeof (sizes[0]))

			__libc_lock_lock (ar_ptr->mutex);

			for (size_t i = 0; i < NFASTBINS; ++i)
	{
		mchunkptr p = fastbin (ar_ptr, i);
		if (p != NULL)
			{
				size_t nthissize = 0;
				size_t thissize = chunksize (p);

				while (p != NULL)
		{
			++nthissize;
			p = p->fd;
		}

				fastavail += nthissize * thissize;
				nfastblocks += nthissize;
				sizes[i].from = thissize - (MALLOC_ALIGNMENT - 1);
				sizes[i].to = thissize;
				sizes[i].count = nthissize;
			}
		else
			sizes[i].from = sizes[i].to = sizes[i].count = 0;

		sizes[i].total = sizes[i].count * sizes[i].to;
	}


			mbinptr bin;
			struct malloc_chunk *r;

			for (size_t i = 1; i < NBINS; ++i)
	{
		bin = bin_at (ar_ptr, i);
		r = bin->fd;
		sizes[NFASTBINS - 1 + i].from = ~((size_t) 0);
		sizes[NFASTBINS - 1 + i].to = sizes[NFASTBINS - 1 + i].total
						= sizes[NFASTBINS - 1 + i].count = 0;

		if (r != NULL)
			while (r != bin)
				{
		size_t r_size = chunksize_nomask (r);
		++sizes[NFASTBINS - 1 + i].count;
		sizes[NFASTBINS - 1 + i].total += r_size;
		sizes[NFASTBINS - 1 + i].from
			= MIN (sizes[NFASTBINS - 1 + i].from, r_size);
		sizes[NFASTBINS - 1 + i].to = MAX (sizes[NFASTBINS - 1 + i].to,
							r_size);

		r = r->fd;
				}

		if (sizes[NFASTBINS - 1 + i].count == 0)
			sizes[NFASTBINS - 1 + i].from = 0;
		nblocks += sizes[NFASTBINS - 1 + i].count;
		avail += sizes[NFASTBINS - 1 + i].total;
	}

			size_t heap_size = 0;
			size_t heap_mprotect_size = 0;
			size_t heap_count = 0;
			if (ar_ptr != &main_arena)
	{
		/* Iterate over the arena heaps from back to front.	*/
		heap_info *heap = heap_for_ptr (top (ar_ptr));
		do
			{
				heap_size += heap->size;
				heap_mprotect_size += heap->mprotect_size;
				heap = heap->prev;
				++heap_count;
			}
		while (heap != NULL);
	}

			__libc_lock_unlock (ar_ptr->mutex);

			total_nfastblocks += nfastblocks;
			total_fastavail += fastavail;

			total_nblocks += nblocks;
			total_avail += avail;

			for (size_t i = 0; i < nsizes; ++i)
	if (sizes[i].count != 0 && i != NFASTBINS)
		fprintf (fp, "										\
	<size from=\"%zu\" to=\"%zu\" total=\"%zu\" count=\"%zu\"/>\n",
			sizes[i].from, sizes[i].to, sizes[i].total, sizes[i].count);

			if (sizes[NFASTBINS].count != 0)
	fprintf (fp, "\
	<unsorted from=\"%zu\" to=\"%zu\" total=\"%zu\" count=\"%zu\"/>\n",
		sizes[NFASTBINS].from, sizes[NFASTBINS].to,
		sizes[NFASTBINS].total, sizes[NFASTBINS].count);

			total_system += ar_ptr->system_mem;
			total_max_system += ar_ptr->max_system_mem;

			fprintf (fp,
				"</sizes>\n<total type=\"fast\" count=\"%zu\" size=\"%zu\"/>\n"
				"<total type=\"rest\" count=\"%zu\" size=\"%zu\"/>\n"
				"<system type=\"current\" size=\"%zu\"/>\n"
				"<system type=\"max\" size=\"%zu\"/>\n",
				nfastblocks, fastavail, nblocks, avail,
				ar_ptr->system_mem, ar_ptr->max_system_mem);

			if (ar_ptr != &main_arena)
	{
		fprintf (fp,
			"<aspace type=\"total\" size=\"%zu\"/>\n"
			"<aspace type=\"mprotect\" size=\"%zu\"/>\n"
			"<aspace type=\"subheaps\" size=\"%zu\"/>\n",
			heap_size, heap_mprotect_size, heap_count);
		total_aspace += heap_size;
		total_aspace_mprotect += heap_mprotect_size;
	}
			else
	{
		fprintf (fp,
			"<aspace type=\"total\" size=\"%zu\"/>\n"
			"<aspace type=\"mprotect\" size=\"%zu\"/>\n",
			ar_ptr->system_mem, ar_ptr->system_mem);
		total_aspace += ar_ptr->system_mem;
		total_aspace_mprotect += ar_ptr->system_mem;
	}

			fputs ("</heap>\n", fp);
			ar_ptr = ar_ptr->next;
		}
	while (ar_ptr != &main_arena);

	fprintf (fp,
		"<total type=\"fast\" count=\"%zu\" size=\"%zu\"/>\n"
		"<total type=\"rest\" count=\"%zu\" size=\"%zu\"/>\n"
		"<total type=\"mmap\" count=\"%d\" size=\"%zu\"/>\n"
		"<system type=\"current\" size=\"%zu\"/>\n"
		"<system type=\"max\" size=\"%zu\"/>\n"
		"<aspace type=\"total\" size=\"%zu\"/>\n"
		"<aspace type=\"mprotect\" size=\"%zu\"/>\n"
		"</malloc>\n",
		total_nfastblocks, total_fastavail, total_nblocks, total_avail,
		mp_.n_mmaps, mp_.mmapped_mem,
		total_system, total_max_system,
		total_aspace, total_aspace_mprotect);

	return 0;
}
weak_alias (__malloc_info, malloc_info)


strong_alias (__libc_calloc, __calloc) weak_alias (__libc_calloc, calloc)
strong_alias (__libc_free, __free) strong_alias (__libc_free, free)
strong_alias (__libc_malloc, __malloc) strong_alias (__libc_malloc, malloc)
strong_alias (__libc_memalign, __memalign)
weak_alias (__libc_memalign, memalign)
strong_alias (__libc_realloc, __realloc) strong_alias (__libc_realloc, realloc)
strong_alias (__libc_valloc, __valloc) weak_alias (__libc_valloc, valloc)
strong_alias (__libc_pvalloc, __pvalloc) weak_alias (__libc_pvalloc, pvalloc)
strong_alias (__libc_mallinfo, __mallinfo)
weak_alias (__libc_mallinfo, mallinfo)
strong_alias (__libc_mallopt, __mallopt) weak_alias (__libc_mallopt, mallopt)

weak_alias (__malloc_stats, malloc_stats)
weak_alias (__malloc_usable_size, malloc_usable_size)
weak_alias (__malloc_trim, malloc_trim)

#if SHLIB_COMPAT (libc, GLIBC_2_0, GLIBC_2_26)
compat_symbol (libc, __libc_free, cfree, GLIBC_2_0);
#endif

/* ------------------------------------------------------------
	History:

	[see ftp://g.oswego.edu/pub/misc/malloc.c for the history of dlmalloc]

 */
/*
 * Local variables:
 * c-basic-offset: 2
 * End:
 */