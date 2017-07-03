#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>


int *
block_create (int i) {

  int *mem=
    calloc (i, sizeof (int));

  if (mem == NULL)
    { perror ("malloc"); exit (1); }
  /*printf("[G-block_create] block : %p\n",mem);*/
  return mem;
  
}

void
block_set (int *bloc, int index, int value) {

  /*printf("[G-block_set_direct] index: %d\n",index);
  printf("[G-block_set_direct] block : %p\n",bloc);*/

  bloc[index]= value;
  
}

int
block_get (int *bloc, int index) {

  int data;
  /*printf("[G-block_get] index: %d\n",index);
  printf("[G-block_get] value : %p\n",bloc);*/
  data= bloc [index];
  
  return data;

}

void 
print_int(int v){
  printf("%d\n",v);
}