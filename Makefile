all:
	gcc -Wall -O3 -march=nocona -c main.c compute.c grobner.c helper.c pol.c scalar.c
	gcc -O3 -march=nocona -o tester main.o compute.o grobner.o helper.o pol.o scalar.o

clean:
	rm -f tester tijdelijk gmon.out
	rm -f basis.o  compute.o  delta.o  grobner.o  helper.o  pol.o  reduce.o  scalar.o test_scalars.o make_list.o

debug:
	gcc -g -DKIJKEN -Wall -pedantic -std=c99 -c main.c  compute.c  grobner.c  helper.c  pol.c  scalar.c
	gcc -g -Wall -o *.o

profiler:
	gcc -g -pg -march=nocona -Wall -c main.c  compute.c  grobner.c  helper.c  pol.c  scalar.c
	gcc -g -pg -Wall -march=nocona -o tester  main.o  compute.o  grobner.o  helper.o  pol.o  scalar.o

test:
	gcc -O3 -Wall -c scalar.c pol.c helper.c test_scalars.c
	gcc -O3 -Wall -o tester test_scalars.o pol.o helper.o scalar.o

make_list:
	gcc -O3 -DLIST_F -Wall -c make_list.c delta.c compute.c grobner.c helper.c pol.c scalar.c
	gcc -O3 -o tester make_list.o delta.o compute.o grobner.o helper.o pol.o scalar.o

random_list:
	gcc -O3 -DLIST_F -Wall -c random_list.c delta.c compute.c grobner.c helper.c pol.c scalar.c
	gcc -O3 -o tester random_list.o delta.o compute.o grobner.o helper.o pol.o scalar.o

input_pol:
	gcc -DINPUT_F -Wall -O3 -march=nocona -c main.c compute.c delta.c grobner.c  helper.c pol.c scalar.c
	gcc -O3 -march=nocona -o tester main.o compute.o delta.o grobner.o helper.o pol.o scalar.o

output_pol:
	gcc -DINPUT_F -DOUTPUT_LIST -Wall -c basis.c  compute.c  delta.c  grobner.c  helper.c  pol.c  reduce.c  scalar.c
	gcc -Wall -o tester basis.o  compute.o  delta.o  grobner.o  helper.o  pol.o  reduce.o  scalar.o
