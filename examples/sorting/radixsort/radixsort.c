/*http://en.wikipedia.org/wiki/Radix_sort#Example_in_C*/
#include<stdio.h>
#include <stdlib.h>

void radixsort(int *a, int n)
{
  int *b = (int *)malloc(n*sizeof(int));
  int i, m = a[0], exp = 1;
  for (i = 0; i < n; i++)
  {
    if (a[i] > m)
      m = a[i];
  }
 
  while (m / exp > 0)
  {
    int bucket[10] =
    {  0 };
    for (i = 0; i < n; i++)
      bucket[a[i] / exp % 10]++;
    for (i = 1; i < 10; i++)
      bucket[i] += bucket[i - 1];
    for (i = n - 1; i >= 0; i--)
      b[--bucket[a[i] / exp % 10]] = a[i];
    for (i = 0; i < n; i++)
      a[i] = b[i];
    exp *= 10;
  }
}

int main(int argc, char *argv[]) {
         
          unsigned int asize;
          int i,sample_count;
          FILE *fp,*fp1;
          fp = fopen(argv[1],"r");
          fp1 = fopen(argv[2],"a");
          fscanf(fp, "%d", &asize);
	  //printf("\nasize =%d\n",asize);
	  int *a = (int *)malloc(asize*sizeof(int));
          for(i=0;i<asize;i++){
             fscanf(fp, "%d", &a[i]);
	     //printf("\na[%d] =%d\n",i,a[i]);                       
	  }  
          radixsort(a, asize);
          for(i=0;i<asize-1;i++){
             fprintf(fp1,"%d ",a[i]);
	  }	  
	  fprintf(fp1,"%d\n",a[i]);
          free(a);
          fclose(fp);
	  fclose(fp1);
	  return 0;
	}

