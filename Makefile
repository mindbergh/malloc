MAKEFLAGS = -j4
CC = gcc
CFLAGS = -Wall -Wextra -Werror -pedantic -g -DDRIVER -std=gnu99
FAST = -DNDEBUG -O2

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o
DEBUG_OBJS = $(patsubst %.o, %.do, $(OBJS))

all: mdriver.fast mdriver.debug

mdriver.fast: $(OBJS)
	$(CC) $(CFLAGS) $(FAST) -o mdriver.fast $(OBJS)

mdriver.debug: $(DEBUG_OBJS)
	$(CC) $(CFLAGS) -o mdriver.debug $(DEBUG_OBJS)

%.o: %.c
	$(CC) $(CFLAGS) $(FAST) -c $< -o $@

%.do: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f *~ *.o *.do mdriver.fast mdriver.debug
