
CFLAGS=-Wall -O2 -g -I.
#debug
#CFLAGS=-Wall -g

LDFLAGS=-lpthread

HOSTTYPE=$(shell uname -m)

ifeq ("${HOSTTYPE}","x86_64")
ARCHTYPE=x86
endif
ifeq ("${HOSTTYPE}","i586")
ARCHTYPE=x86
endif
ifeq ("${HOSTTYPE}","i686")
ARCHTYPE=x86
endif
ifeq ("${HOSTTYPE}","powerpc")
ARCHTYPE=ppc
endif
ifeq ("${HOSTTYPE}","ppc64")
ARCHTYPE=ppc
endif
ifeq ("${HOSTTYPE}","s390")
ARCHTYPE=s390
endif
ifeq ("${HOSTTYPE}","s390x")
ARCHTYPE=s390
endif

#Build the library without using signals. Slower read-side.
#CFLAGS+=-DCONFIG_URCU_AVOID_SIGNALS

#Changing the signal number used by the library. SIGUSR1 by default.
#CFLAGS+=-DSIGURCU=SIGUSR2

SRC_DEP=`echo $^ | sed 's/[^ ]*\.h//g'`
