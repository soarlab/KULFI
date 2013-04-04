/*http://p2p.wrox.com/visual-c/66347-quick-sort-c-code.html*/
#include <stdlib.h>
#include <stdio.h>

void q_sort(int numbers[], int left, int right)
{
  int pivot, l_hold, r_hold;
 
  l_hold = left;
  r_hold = right;
  pivot = numbers[left];
  while (left < right)
  {
    while ((numbers[right] >= pivot) && (left < right))
      right--;
    if (left != right)
    {
      numbers[left] = numbers[right];
      left++;
    }
    while ((numbers[left] <= pivot) && (left < right))
      left++;
    if (left != right)
    {
      numbers[right] = numbers[left];
      right--;
    }
  }
  numbers[left] = pivot;
  pivot = left;
  left = l_hold;
  right = r_hold;
  if (left < pivot)
    q_sort(numbers, left, pivot-1);
  if (right > pivot)
    q_sort(numbers, pivot+1, right);
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
          q_sort(a, 0, asize - 1);
          for(i=0;i<asize-1;i++){
             fprintf(fp1,"%d ",a[i]);
	  }	  
	  fprintf(fp1,"%d\n",a[i]);
          free(a);
          fclose(fp);
	  fclose(fp1);
	  return 0;
	}
