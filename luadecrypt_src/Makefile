CC= gcc
CFLAGS= -O2 -Wall -fPIC -I../lua_vm/lua
LDFLAGS= -shared

OBJS= ../lua_vm/lua/lapi.o ../lua_vm/lua/lcode.o ../lua_vm/lua/lctype.o       ../lua_vm/lua/ldebug.o ../lua_vm/lua/ldo.o ../lua_vm/lua/ldump.o       ../lua_vm/lua/lfunc.o ../lua_vm/lua/lgc.o ../lua_vm/lua/llex.o       ../lua_vm/lua/lmem.o ../lua_vm/lua/lobject.o ../lua_vm/lua/lopcodes.o       ../lua_vm/lua/lparser.o ../lua_vm/lua/lstate.o ../lua_vm/lua/lstring.o       ../lua_vm/lua/ltable.o ../lua_vm/lua/ltm.o ../lua_vm/lua/lundump.o       ../lua_vm/lua/lvm.o ../lua_vm/lua/lzio.o ../lua_vm/lua/lobfuscator.o       ../lua_vm/lua/lsha256.o

all: luadecrypt.so

luadecrypt.so: luadecrypt.o
	$(CC) $(LDFLAGS) -o $@ luadecrypt.o $(OBJS) -lm

luadecrypt.o: luadecrypt.c
	$(CC) $(CFLAGS) -c luadecrypt.c -o $@

clean:
	rm -f *.o *.so
