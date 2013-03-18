/*******************************************************************************************/
/* Name        : Corrupt.c                                                                 */
/* Description : This file contains code for corrupting data and pointer. It is linked at  */
/*               compiled time to the target code where fault(s) need to be injected       */
/*      									   */
/* Owner       : This tool is owned by Gauss Research Group at School of Computing,        */
/*               University of Utah, Salt Lake City, USA.                                  */
/*               Please send your queries to: gauss@cs.utah.edu                            */
/*               Researh Group Home Page: http://www.cs.utah.edu/formal_verification/      */
/* Version     : beta									   */
/* Last Edited : 03/12/2013                                                                */
/* Copyright   : Refer to LICENSE document for details 					   */
/*******************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int rand_flag=1;
int rand_flagL=1;
int rand_flagA=1;
int ijo_flag=0;
int ijo_flagA=0;
int fault_injection_count=0;

int corrupt(int fault_index, int inject_once, int ef, int tf, int byte_val, int inst_data){
   unsigned int bPos;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }    
   int rp = rand()%tf+1;

   if(inject_once == 1)
     ijo_flag=1;

   if(ijo_flag == 1 && fault_injection_count>0){
       return inst_data;        
   }
   if(rp>ef){
       return inst_data;
   }
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 32-bit data error!!");
   printf("\nInject Once Flag is : %d",inject_once);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nByte position is: %d",byte_val);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\n/*********************************End**************************************/\n");
   if(byte_val>3)
      bPos=(8*(byte_val-4))+rand()%8;
   else
      bPos=(8*byte_val)+rand()%8;

   fault_injection_count++;
   if ((inst_data>>bPos)&0x1)
     return inst_data & (~(0x1<< (rand()%32)));   
   else
     return inst_data |  (0x1<< (rand()%32));
   
}
 
int* corrupt_Add(int fault_index, int inject_once, int ef, int tf,  int byte_val, int* inst_add){
   unsigned int bPos;
   if(rand_flagA){
      srand(time(NULL));
      rand_flagA=0;
   }    
   int rp = rand()%tf+1;
   if(inject_once == 1)
     ijo_flagA=1;

   if(ijo_flagA == 1 && fault_injection_count>0)
       return inst_add;           

   if(rp>ef)
       return inst_add;
   
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 32-bit data error!!");
   printf("\nInject Once Flag is : %d",inject_once);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nByte position is: %d",byte_val);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\n/*********************************End**************************************/\n");

   if(byte_val>3)
      bPos=(8*(byte_val-4))+rand()%8;
   else
      bPos=(8*byte_val)+rand()%8;

   fault_injection_count++;
   if (((int)inst_add>>bPos)&0x1)
     return (int *)((int)inst_add & (~(0x1<< (rand()%32))));   
   else
     return (int *)((int)inst_add |  (0x1<< (rand()%32)));
   
}

long long corruptL(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long inst_data){
   if(rand_flagL){
      srand(time(NULL));
      rand_flagL=0;
   }    
   int rp = rand()%tf+1;

   if(inject_once == 1)
     ijo_flag=1;

   if(ijo_flag == 1 && fault_injection_count>0)
       return inst_data;        
   
   if(rp>ef)
       return inst_data;
   
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 32-bit data error!!");
   printf("\nInject Once Flag is : %d",inject_once);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nByte position is: %d",byte_val);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\n/*********************************End**************************************/\n");

   unsigned int bPos=(8*byte_val)+rand()%8;

   fault_injection_count++;
   if ((inst_data>>bPos)&0x1)
     return inst_data & (long long) (~(0x1<< (rand()%64)));   
   else
     return inst_data | (long long) (0x1<< (rand()%64));
   
}
