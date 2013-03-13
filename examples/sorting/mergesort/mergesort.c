/*Source:http://www.thelearningpoint.net/computer-science/arrays-and-sorting-merge-sort--with-c-program-source-code*/
#include<stdio.h>
#include <stdlib.h>
void Merge(int * , int , int , int );
void MergeSort(int *array, int left, int right)
{
        int mid = (left+right)/2;
        if(left<right)
        {
                /* Sort the left part */
                MergeSort(array,left,mid);
                /* Sort the right part */
                MergeSort(array,mid+1,right);
                /* Merge the two sorted parts */
                Merge(array,left,mid,right);
        }
}
void Merge(int *array, int left, int mid, int right)
{
        int tempArray[right-left+1];
        int pos=0,lpos = left,rpos = mid + 1;
        while(lpos <= mid && rpos <= right)
        {
                if(array[lpos] < array[rpos])
                {
                        tempArray[pos++] = array[lpos++];
                }
                else
                {
                        tempArray[pos++] = array[rpos++];
                }
        }
        while(lpos <= mid)  tempArray[pos++] = array[lpos++];
        while(rpos <= right)tempArray[pos++] = array[rpos++];
        int iter;
        for(iter = 0;iter < pos; iter++)
        {
                array[iter+left] = tempArray[iter];
        }
        return;
}
int main(int argc, char *argv[]) {
         
          unsigned int asize;
          int i,sample_count;
      //    FILE *fp,*fp1;
        //  fp = fopen(argv[1],"r");
          fp1 = fopen(argv[2],"a");
          fscanf(fp, "%d", &asize);
	  //printf("\nasize =%d\n",asize);
	  int *a = (int *)malloc(asize*sizeof(int));
          for(i=0;i<asize;i++){
             fscanf(fp, "%d", &a[i]);
	     //printf("\na[%d] =%d\n",i,a[i]);                       
	  }  
          MergeSort(a, 0, asize - 1);
          for(i=0;i<asize-1;i++){
             fprintf(fp1,"%d ",a[i]);
	  }	  
	  fprintf(fp1,"%d\n",a[i]);
          free(a);
          fclose(fp);
	  fclose(fp1);
	  return 0;
	}

