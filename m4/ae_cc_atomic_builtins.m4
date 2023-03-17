# SYNOPSIS
#
#   AE_CC_ATOMIC_BUILTINS([ACTION-IF-FOUND[, ACTION-IF-NOT-FOUND]])
#
# LICENSE
#
#   Copyright (c) 2023 Michael Jeanson <mjeanson@efficios.com>
#
#   This program is free software; you can redistribute it and/or modify it
#   under the terms of the GNU General Public License as published by the
#   Free Software Foundation; either version 2 of the License, or (at your
#   option) any later version.
#
#   This program is distributed in the hope that it will be useful, but
#   WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General
#   Public License for more details.
#
#   You should have received a copy of the GNU General Public License along
#   with this program. If not, see <https://www.gnu.org/licenses/>.
#
#   As a special exception, the respective Autoconf Macro's copyright owner
#   gives unlimited permission to copy, distribute and modify the configure
#   scripts that are the output of Autoconf when processing the Macro. You
#   need not follow the terms of the GNU General Public License when using
#   or distributing such scripts, even though portions of the text of the
#   Macro appear in them. The GNU General Public License (GPL) does govern
#   all other use of the material that constitutes the Autoconf Macro.
#
#   This special exception to the GPL applies to versions of the Autoconf
#   Macro released by the Autoconf Archive. When you make and distribute a
#   modified version of the Autoconf Macro, you may extend this special
#   exception to the GPL to apply to your modified version as well.

#serial 1

AC_DEFUN([AE_CC_ATOMIC_BUILTINS], [
AC_REQUIRE([AC_PROG_CC])
AC_LANG_PUSH([C])

AC_CACHE_CHECK(
  [whether $CC supports atomic builtins],
  [ae_cv_cc_atomic_builtins],
  [
    AC_LINK_IFELSE([
      AC_LANG_PROGRAM([
        int x, y;
      ],[
        __atomic_store_n(&x, 0, __ATOMIC_RELAXED);
        __atomic_load_n(&x, __ATOMIC_RELAXED);
        y = __atomic_exchange_n(&x, 1, __ATOMIC_RELAXED);
        __atomic_compare_exchange_n(&x, &y, 0, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED);
        __atomic_add_fetch(&x, 1, __ATOMIC_RELAXED);
        __atomic_sub_fetch(&x, 1, __ATOMIC_RELAXED);
        __atomic_and_fetch(&x, 0x01, __ATOMIC_RELAXED);
        __atomic_or_fetch(&x, 0x01, __ATOMIC_RELAXED);
        __atomic_thread_fence(__ATOMIC_RELAXED);
        __atomic_signal_fence(__ATOMIC_RELAXED);
      ])
    ],[
      ae_cv_cc_atomic_builtins=yes
    ],[
      ae_cv_cc_atomic_builtins=no
    ])
  ]
)

# Finally, execute ACTION-IF-FOUND/ACTION-IF-NOT-FOUND:
if test "x$ae_cv_cc_atomic_builtins" = "xyes"; then
  $1
  :
else
  $2
  :
fi

AC_LANG_POP
])dnl AE_CC_ATOMIC_BUILTINS
