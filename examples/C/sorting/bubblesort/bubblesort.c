/*Source:http://www.algorithmist.com/index.php/Bubble_sort.c*/

#include <stdio.h>
#include <stdlib.h>

void bubbleSort(int numbers[], int array_size)
{
  int i, j, temp;
 
  for (i = (array_size - 1); i > 0; i--)
  {
    for (j = 1; j <= i; j++)
    {
      if (numbers[j-1] > numbers[j])
      {
        temp = numbers[j-1];
        numbers[j-1] = numbers[j];
        numbers[j] = temp;
      }
    }
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
          //printf("\nStarting bubble sort for array of size =%d",asize);                       
          bubbleSort(a,asize);
          for(i=0;i<asize-1;i++){
             fprintf(fp1,"%d ",a[i]);
	  }	  
	  fprintf(fp1,"%d\n",a[i]);
          //printf("\nEnding bubble sort for array of size =%d",asize);                       
          free(a);
          fclose(fp);
	  fclose(fp1);
	  return 0;
	}
