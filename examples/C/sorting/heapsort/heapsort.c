/*http://www.algorithmist.com/index.php/Heap_sort.c*/
#include<stdio.h>
#include <stdlib.h>

void siftDown(int numbers[], int root, int bottom) {
  int maxChild = root * 2 + 1;
 
  // Find the biggest child
  if(maxChild < bottom) {
    int otherChild = maxChild + 1;
    // Reversed for stability
    maxChild = (numbers[otherChild] > numbers[maxChild])?otherChild:maxChild;
  } else {
    // Don't overflow
    if(maxChild > bottom) return;
  }
 
  // If we have the correct ordering, we are done.
  if(numbers[root] >= numbers[maxChild]) return;
 
  // Swap
  int temp = numbers[root];
  numbers[root] = numbers[maxChild];
  numbers[maxChild] = temp;
 
  // Tail queue recursion. Will be compiled as a loop with correct compiler switches.
  siftDown(numbers, maxChild, bottom);
}


void heapSort(int numbers[], int array_size) {
  int i, temp;
 
  for (i = (array_size / 2); i >= 0; i--) {
    siftDown(numbers, i, array_size - 1);
  }
 
  for (i = array_size-1; i >= 1; i--) {
    // Swap
    temp = numbers[0];
    numbers[0] = numbers[i];
    numbers[i] = temp;
 
    siftDown(numbers, 0, i-1);
  }
}

int main(int argc, char *argv[]) {
         
          unsigned int asize;
          int i,sample_count;
          FILE *fp,*fp1;
          fp = fopen(argv[1],"r");
          fp1 = fopen(argv[2],"a");
          fscanf(fp, "%d", &asize);
	  printf("\nasize =%d\n",asize);
	  int *a = (int *)malloc(asize*sizeof(int));
          for(i=0;i<asize;i++){
             fscanf(fp, "%d", &a[i]);
	     //printf("\na[%d] =%d\n",i,a[i]);                       
	  }  
          heapSort(a, asize);
          for(i=0;i<asize-1;i++){
             fprintf(fp1,"%d ",a[i]);
	  }	  
	  fprintf(fp1,"%d\n",a[i]);
          free(a);
          fclose(fp);
	  fclose(fp1);
	  return 0;
	}


