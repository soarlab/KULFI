#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <math.h>
#include <string.h>
#include <map>

int num_verts = 0;
float* edge_costs = NULL;
#define IDX(i,j) (i*num_verts+j)
#define BIG 2000000000

const int DBG = 0;

/////////////////////////////////////////
typedef unsigned int mask_t;
const int NUM_BITS_PER_MASK = sizeof(mask_t)*8; // A char has 8 bits

inline int NumOfBitsSet(const mask_t& bitmask) {
	int bm = 0x01, ret = 0;
	for(int i=0; i<NUM_BITS_PER_MASK; i++) {
		if((bm & bitmask) == bm) ret++;
		bm = bm << 1;
	}
	return ret;
}

int PrintBitMask(const mask_t& bitmask) {
	mask_t m = 1<<(NUM_BITS_PER_MASK-1);
	for(int i=0; i<NUM_BITS_PER_MASK; i++) {
		if((m&bitmask)==m) printf("1");
		else printf("0");
		m=(m>>1);
	}
	printf("\n");
	return 0;
}

void SetBit(mask_t& bitmask, int bitidx) {
//	assert((bitidx>=0) && (bitidx<NUM_BITS_PER_MASK));
	bitmask |= (0x01 << bitidx);
}

void UnsetBit(mask_t& bitmask, int bitidx) {
//	assert((bitidx>=0) && (bitidx<NUM_BITS_PER_MASK));
	bitmask &= (~(0x01 << bitidx));
}

int IsBitSet(const mask_t& bitmask, int bitidx) {
//	assert((bitidx>=0) && (bitidx<NUM_BITS_PER_MASK));
	mask_t m1 = (0x01 << bitidx);
	if((m1 & bitmask)==m1) return 1;
	else return 0;
}

int IdxOfLastOne(const mask_t& bitmask) {
	int ret = NUM_BITS_PER_MASK-1;
	while((ret >= 0) && (IsBitSet(bitmask, ret)==0)) ret=ret-1;
	return ret;
}

/////////////////////////////////////////
std::map<mask_t, std::map<int, float> > costmap1;
std::map<mask_t, std::map<int, float> > costmap2;
std::map<mask_t, std::map<int, float> > *costmap_curr, *costmap_prev, *tmp;

/////////////////////////////////////////

void test();

int main(int argc, char** argv) {

	printf("Num of bits per mask = %d\n", NUM_BITS_PER_MASK);

	if(argc < 2) {
		printf("Usage 1: a.out tsp.txt\n");
		printf("Usage 2: a.out test\n");
		exit(0);
	}

	if(strcmp(argv[1], "test")==0) {
		test();
		exit(0);
	}

	FILE* f = fopen(argv[1], "r");
	if(!f) { printf("Oh! Can't open file %s.\n", argv[1]); exit(0); }

	assert(fscanf(f, "%d", &num_verts)==1);
	printf("%d vertices.\n", num_verts);
	if(num_verts > NUM_BITS_PER_MASK) {
		printf("Oh! Curr impl only supports <= %d vertices. Exiting.\n", NUM_BITS_PER_MASK);
		exit(0);
	}

	edge_costs = (float*)malloc(sizeof(float)*num_verts*num_verts);
	float* vx = (float*)malloc(sizeof(float) * num_verts);
	float* vy = (float*)malloc(sizeof(float) * num_verts);

	// Read vertices
	for(int i=0; i<num_verts; i++) {
		fscanf(f, "%g %g", &vx[i], &vy[i]);
	}

	// Fill in edge cost table
	printf("Fill in edge cost table.\n");
	for(int i=0; i<num_verts; i++) {
		for(int j=0; j<num_verts; j++) {
			if(i==j) { edge_costs[IDX(i,j)]=0; continue; }
			else {
				float dx=vx[i]-vx[j], dy=vy[i]-vy[j];
				edge_costs[IDX(i,j)]=edge_costs[IDX(j,i)]=sqrt(dx*dx + dy*dy);
			}
		}
	}

	// prepare.
	mask_t bm0 = 0x00000000;
	costmap_prev = &costmap1;
	costmap_curr = &costmap2;
	for(int i=1; i<num_verts; i++) {
		(*costmap_prev)[bm0][i] = edge_costs[IDX(i, 0)];
	}

	float g_cost_min = BIG;
	for(int iter=0; iter<num_verts-1; iter++)
	{
		printf("Iteration #%d\n", iter);
		std::map<mask_t, std::map<int, float> >::iterator cm_begin = (*costmap_prev).begin();
		std::map<mask_t, std::map<int, float> >::iterator cm_end   = (*costmap_prev).end();

		std::map<mask_t, std::map<int, float> >::iterator itr = cm_begin;
		printf("Costmap has %lu entries.\n", costmap_prev->size());

		if(DBG)
		{
			// Print it all
			std::map<mask_t, std::map<int, float> >::iterator itr = costmap_prev->begin();
			for(; itr!=costmap_prev->end(); itr++) {
				PrintBitMask(itr->first);
				std::map<int, float> map2 = itr->second;
				std::map<int, float>::iterator itr2 = map2.begin();
				for(; itr2!=map2.end(); itr2++) {
					printf(" %d %g\n", itr2->first, itr2->second);
				}
			}
		}

		int size1 = costmap_prev->size();
		for(; itr!=cm_end; itr++) {
			mask_t bitmask = itr->first;
			std::map<int, float> map2 = itr->second;

				
			// Duct-tape corner case detection.......
			if(iter == num_verts-2) {
				// On the last iteration, it's time to compute overall cost.
//				assert(map2.size()==1);
				std::map<int, float>::iterator m2itr = map2.begin();
				int vert = m2itr->first;
				float cost = edge_costs[IDX(0, vert)] + m2itr->second;
				if(DBG)	{
					printf(">> Cost from 0 to %d to all others to 0: %g\n",
						vert, cost);
				}
				if(cost < g_cost_min) g_cost_min = cost;
				continue;
			}



			// 1. What are the possible next bitmasks ?
			int idx_first0_last1 = IdxOfLastOne(bitmask) + 1;
			if(idx_first0_last1==0) idx_first0_last1=1;
			for(int bitidx=idx_first0_last1; bitidx<num_verts; bitidx++) {
				// 1.5. Generate new bitmaps (used for next iteration)
				mask_t next_mask = bitmask;
				SetBit(next_mask, bitidx);

				// 1.6 For each possible next_mask, compute all possible pred_masks
				for(int v_from=1; v_from<num_verts; v_from++) { // 0 is the reserved guy.
					if(DBG) printf(">>> %d\n", v_from);
					if((IsBitSet(next_mask, v_from)==1)&&NumOfBitsSet(next_mask)!=num_verts-1) continue;
					// Compute the cost of going from node v_from to 0
					// via edges in next_mask
					float cost_min = BIG;
					for(int bit_entr = 1; bit_entr < num_verts; bit_entr++) {
						if(bit_entr == v_from) continue;
						if(IsBitSet(next_mask, bit_entr)==0) continue;
						mask_t pred_mask = next_mask;
						UnsetBit(pred_mask, bit_entr);
						{ // For debugging purpose.
//							assert(costmap_prev->find(pred_mask)!=costmap_prev->end());
							std::map<int, float> map2 = (*costmap_prev)[pred_mask];
//							assert(map2.find(bit_entr) != map2.end());
						}
						float cost_this = edge_costs[IDX(v_from, bit_entr)] +
							(*costmap_prev)[pred_mask][bit_entr];
						if(DBG) {
							printf("ct = %g = %g + %g, %d, %d\n", cost_this,
								edge_costs[IDX(v_from, bit_entr)],
								(*costmap_prev)[pred_mask][bit_entr],
								v_from, bit_entr
							);
						}
						if(cost_this < cost_min) cost_min = cost_this;
					}
					// Now we have A[S,v_from]
					if(costmap_curr->find(next_mask) == costmap_curr->end()) {
						std::map<int, float> tmp;
						(*costmap_curr)[next_mask]=tmp;
					}
					(*costmap_curr)[next_mask][v_from] = cost_min;
				}
			}
		}
//		printf("\n");
		tmp = costmap_prev;
		costmap_prev = costmap_curr;
		costmap_curr = tmp;

		itr = costmap_curr->begin();
		for(; itr!=costmap_curr->end(); itr++) {
			itr->second.clear();
		}
		costmap_curr->clear();
	}

	printf("COST: %g\n", g_cost_min);
	exit(0);

	printf("Sizes: curr=%d, prev=%d.\n", costmap_curr->size(), costmap_prev->size());
//	assert(costmap_prev->size()==1);

	float cost_min = BIG;
	std::map<mask_t, std::map<int, float> >::iterator cm_begin = (*costmap_prev).begin();
	std::map<int, float> map2 = cm_begin->second;
	printf("Final Map2 has %d entries.\n", map2.size());

	for(std::map<int, float>::iterator itr2 = map2.begin(); itr2!=map2.end(); itr2++) {
		float cost = itr2->second + edge_costs[IDX(0, itr2->first)];
		if(cost < cost_min) cost_min = cost;
		printf("%d %g %g\n", itr2->first, itr2->second, cost);
	}
	printf("COST: %g\n", cost_min);
}

void test() {
	mask_t m1=0;
	printf("Num of bits set: %d\n", NumOfBitsSet(m1));
	printf("Idx of last one: %d\n", IdxOfLastOne(m1));
	PrintBitMask(m1);
	printf("\n");
	SetBit(m1, 13);
	printf("Num of bits set: %d\n", NumOfBitsSet(m1));
	printf("Idx of last one: %d\n", IdxOfLastOne(m1));
	PrintBitMask(m1);
	printf("\n");

	std::map<int, std::map<mask_t, int> > map1;
	map1[1][m1] = 123;
	printf("map1[1][m1]=%d\n", map1[1][m1]);
	std::map<int, std::map<mask_t, int> >::iterator got = map1.find(2);
	if(got == map1.end()) {
		printf("Actually map1[2] is not found.\n");
	} else { printf("Acutally map1[2] is found.\n"); }
	printf("map1[2][m1]=%d\n", map1[2][m1]);
}
