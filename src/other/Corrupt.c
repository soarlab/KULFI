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


/*random seed initialization flag*/
int rand_flag=1;

/*Inject Once Status for data and pointer errors*/
int ijo_flag_data=0;
int ijo_flag_add=0;

/*fault injection count*/
int fault_injection_count=0;

/*Fault Injection Statistics*/
int fault_site_count=0;
int fault_site_intData16bit=0;
int fault_site_intData32bit=0;
int fault_site_intData64bit=0;
int fault_site_float32bit=0;
int fault_site_float64bit=0;
int fault_site_adr=0;

int print_faultStatistics(int inject_once, int ef, int tf, int byte_val){
   printf("\n/*********************Fault Injection Statistics****************************/");
   printf("\nTotal # fault sites enumerated : %d",fault_site_count);
   printf("\nFurther sub-categorization of fault sites below:");
   printf("\nTotal # 16-bit Int Data fault sites enumerated : %d",fault_site_intData16bit);
   printf("\nTotal # 32-bit Int Data fault sites enumerated : %d",fault_site_intData32bit);
   printf("\nTotal # 64-bit Int Data fault sites enumerated : %d",fault_site_intData64bit);
   printf("\nTotal # 32-bit IEEE Float Data fault sites enumerated : %d",fault_site_float32bit);
   printf("\nTotal # 64-bit IEEE Float Data fault sites enumerated : %d",fault_site_float64bit);
   printf("\nTotal # Ptr fault sites enumerated : %d",fault_site_adr);
   printf("\n/*********************************End**************************************/\n");
   return 0;
}

short corruptIntData_16bit(int fault_index, int inject_once, int ef, int tf, int byte_val, short inst_data){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_intData16bit++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }    
   if(inject_once == 1)
     ijo_flag_data=1;
   if(ijo_flag_data == 1 && fault_injection_count>0)
       return inst_data;
   
   rp = rand()%tf+1;
   if(rp>ef)
       return inst_data;
   if(byte_val>1)
      bPos=(8*(byte_val%2))+rand()%8;
   else
      bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 16-bit Integer Data error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if ((inst_data>>bPos)&0x1)
     return inst_data & (~((short)0x1<< (bPos)));   
   else
     return inst_data |  ((short)0x1<< (bPos));   
}


int corruptIntData_32bit(int fault_index, int inject_once, int ef, int tf, int byte_val, int inst_data){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_intData32bit++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }    
   if(inject_once == 1)
     ijo_flag_data=1;

   if(ijo_flag_data == 1 && fault_injection_count>0)
       return inst_data;
   
   rp = rand()%tf+1;
   if(rp>ef)
       return inst_data;
   if(byte_val>3)
      bPos=(8*(byte_val%4))+rand()%8;
   else
      bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 32-bit Integer Data error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if ((inst_data>>bPos)&0x1)
     return inst_data & (~((int)0x1<< (bPos)));   
   else
     return inst_data |  ((int)0x1<< (bPos));   
}

float corruptFloatData_32bit(int fault_index, int inject_once, int ef, int tf, int byte_val, float inst_data){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_float32bit++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }    
   if(inject_once == 1)
     ijo_flag_data=1;

   if(ijo_flag_data == 1 && fault_injection_count>0)
       return inst_data;
   
   rp = rand()%tf+1;
   if(rp>ef)
       return inst_data;
   if(byte_val>3)
      bPos=(8*(byte_val%4))+rand()%8;
   else
      bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 32-bit IEEE Float Data error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if (((int)inst_data>>bPos)&0x1)
     return (float)((int)inst_data & (~((int)0x1<< (bPos))));   
   else
     return (float)((int)inst_data |  ((int)0x1<< (bPos)));   
}

long long corruptIntData_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long inst_data){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_intData64bit++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }    
   if(inject_once == 1)
     ijo_flag_data=1;

   if(ijo_flag_data == 1 && fault_injection_count>0)
       return inst_data;        
   
   rp = rand()%tf+1;
   if(rp>ef)
       return inst_data;
   bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 64-bit Integer Data error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if ((inst_data>>bPos)&0x1)
     return inst_data & (~((long long)0x1<< (bPos)));   
   else
     return inst_data | ((long long)0x1<< (bPos));
   
}

double corruptFloatData_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, double inst_data){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_float64bit++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }    
   if(inject_once == 1)
     ijo_flag_data=1;

   if(ijo_flag_data == 1 && fault_injection_count>0)
       return inst_data;        

   rp = rand()%tf+1;
   if(rp>ef)
       return inst_data;
   bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;
   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected 64-bit IEEE Float Data error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if (((long long)inst_data>>bPos)&0x1)
     return (double)((long long)inst_data & (~((long long)0x1<< (bPos))));   
   else
     return (double)((long long)inst_data | ((long long)0x1<< (bPos)));
   
}

int* corruptIntAdr_32bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, int* inst_add){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_adr++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }
   if(inject_once == 1)
     ijo_flag_add=1;

   if(ijo_flag_add == 1 && fault_injection_count>0)
       return inst_add;           

   rp = rand()%tf+1;
   if(rp>ef)
       return inst_add;

   bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;

   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected ptr error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if (((long long)inst_add>>bPos)&0x1)
     return (int *)((long long)inst_add & (~((long long)0x1<< (bPos))));   
   else
     return (int *)((long long)inst_add |  ((long long)0x1<< (bPos)));   
}

long long* corruptIntAdr_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, long long* inst_add){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_adr++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }
   if(inject_once == 1)
     ijo_flag_add=1;

   if(ijo_flag_add == 1 && fault_injection_count>0)
       return inst_add;           

   rp = rand()%tf+1;
   if(rp>ef)
       return inst_add;

   bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;

   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected ptr error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if (((long long)inst_add>>bPos)&0x1)
     return (long long *)((long long)inst_add & (~((long long)0x1<< (bPos))));   
   else
     return (long long *)((long long)inst_add |  ((long long)0x1<< (bPos)));   
}

float* corruptFloatAdr_32bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, float* inst_add){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_adr++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }
   if(inject_once == 1)
     ijo_flag_add=1;

   if(ijo_flag_add == 1 && fault_injection_count>0)
       return inst_add;           

   rp = rand()%tf+1;
   if(rp>ef)
       return inst_add;

   bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;

   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected ptr error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if (((long long)inst_add>>bPos)&0x1)
     return (float *)((long long)inst_add & (~((long long)0x1<< (bPos))));   
   else
     return (float *)((long long)inst_add |  ((long long)0x1<< (bPos)));   
}

double* corruptFloatAdr_64bit(int fault_index, int inject_once, int ef, int tf,  int byte_val, double* inst_add){
   unsigned int bPos;
   int rp;
   fault_site_count++;
   fault_site_adr++;
   if(rand_flag){
      srand(time(NULL));
      rand_flag=0;
   }
   if(inject_once == 1)
     ijo_flag_add=1;

   if(ijo_flag_add == 1 && fault_injection_count>0)
       return inst_add;           

   rp = rand()%tf+1;
   if(rp>ef)
       return inst_add;

   bPos=(8*byte_val)+rand()%8;
   fault_injection_count++;

   printf("\n/*********************************Start**************************************/");
   printf("\nSucceffully injected ptr error!!");
   printf("\nTotal # faults injected : %d",fault_injection_count);
   printf("\nBit position is: %u",bPos);
   printf("\nIndex of the fault site : %d",fault_index);
   printf("\nUser defined probablity is: %d/%d",ef,tf);
   printf("\nChosen random probablity is: %d/%d",rp,tf);   
   printf("\n/*********************************End**************************************/\n");
   if (((long long)inst_add>>bPos)&0x1)
     return (double *)((long long)inst_add & (~((long long)0x1<< (bPos))));   
   else
     return (double *)((long long)inst_add |  ((long long)0x1<< (bPos)));   
}
