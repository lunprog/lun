default: all

all: main lunc

main: main.o hello.o
	gcc main.o hello.o -o main

main.o: main.c
	cc -c main.c -o main.o

hello.o: hello.lun lunc
	../../target/debug/lunc -Coutput-obj=true -Zprint=ssa  --orb-name hello hello.lun

lunc: ../../target/debug/lunc
	cargo build -q --bin lunc

run: all
	./main
