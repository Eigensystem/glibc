/* Syscall definitions, Linux PowerPC generic version.
   Copyright (C) 2019 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <http://www.gnu.org/licenses/>.  */

#define VDSO_NAME  "LINUX_2.6.15"
#define VDSO_HASH  123718565

/* List of system calls which are supported as vsyscalls.  */
#define HAVE_CLOCK_GETRES_VSYSCALL	1
#define HAVE_CLOCK_GETTIME_VSYSCALL	1
#define HAVE_GETCPU_VSYSCALL		1