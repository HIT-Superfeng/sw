/*
 * Copyright 2017 International Business Machines
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *	 http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <errno.h>
#include <malloc.h>
#include <unistd.h>
#include <sys/time.h>
#include <time.h>
#include <getopt.h>
#include <ctype.h>
#include "rsa.h"
#include <stdint.h>
#include <libsnap.h>
#include <snap_tools.h>
#include <snap_s_regs.h>

#include "hdl_rsa.h"

/*  defaults */
#define ACTION_WAIT_TIME	10   /* Default in sec */

#define MEGAB	   (1024*1024ull)
#define GIGAB	   (1024 * MEGAB)

#define VERBOSE0(fmt, ...) do {		 \
		printf(fmt, ## __VA_ARGS__);	\
	} while (0)

#define VERBOSE1(fmt, ...) do {		 \
		if (verbose_level > 0)		  \
			printf(fmt, ## __VA_ARGS__);	\
	} while (0)

#define VERBOSE2(fmt, ...) do {		 \
		if (verbose_level > 1)		  \
			printf(fmt, ## __VA_ARGS__);	\
	} while (0)


#define VERBOSE3(fmt, ...) do {		 \
		if (verbose_level > 2)		  \
			printf(fmt, ## __VA_ARGS__);	\
	} while (0)

#define VERBOSE4(fmt, ...) do {		 \
		if (verbose_level > 3)		  \
			printf(fmt, ## __VA_ARGS__);	\
	} while (0)


uint64_t key[16] = {0x3d90583967fa0eb0, 0xc094be7364566069,
                  0x671dbd6b22789495, 0x0c799eb6df85016e,
                  0x69a73707911072dc, 0x79306d7b7c39d17b,
                  0x91b093738a767095, 0xbfc2f0c9101d46e9,
                  0xf5c6223bcec81fbe, 0xdf27daa04435d5e8,
                  0x62edf78af08df2e8, 0x0e0d848d31d1bc33,
                  0x0d0c7eab45fe4793, 0x5cbb220553202552,
                  0x2886872ff402809f, 0x5f90bc842c665d59};

uint64_t mod[16] = {0xe33f163d5abb6400, 0x570f33f1b25c2f2c,
                  0x971fd4105c60de34, 0xbb24aaf5c751996c,
                  0x51f5ba457738cb26, 0xc5d326cb1bc7af83,
                  0xee0a9994e35e3894, 0xe8b60b438cbcc0cb,
                  0xaa9b0f068b87c2b2, 0x54024d33b2e8a927,
                  0x471f65e96bdb5997, 0x9d1cbee8f9da1ec9,
                  0xc3ffc485169443b0, 0xc21571d8e2cf318e,
                  0xcf70c65159268afe, 0x2e53ed42cdc830d3};

uint64_t data[16] = {0xceba9238407ed164, 0x5c01d7a77e2db319,
                   0x46f16faa0778db7d, 0xfe205dc4ba651402,
                   0x1d59a408800cac79, 0x84c68e4157181a98,
                   0xc44028162d8aee20, 0x95b4d1e63392f980,
                   0x816881f87cc4866a, 0xd06b449ce990f8a9,
                   0xe459a1c9398181dd, 0x9296230bdb7e288c,
                   0x5b41a4fbb2686c03, 0x18d03b4b1af7640f,
                   0xa0471f0370fff32f, 0xc6f760cab80b0acd};
				








static const char* version = GIT_VERSION;
static  int verbose_level = 0;

void temp_disp(uint64_t x[], uint32_t n);
uint64_t x[20]={0},y[20]={0},z[20]={0},e[18]={0};

bool rsa1024(uint64_t res[], uint64_t data[], uint64_t expo[],uint64_t key[])
{
    int32_t i,j,expo_len;
    uint64_t mod_data[18]={0},result[18]={0};
    uint64_t temp_expo=0;

    modbignum(mod_data,data,key,16);
    result[0] = 1;
    expo_len = bit_length(expo,16) /64;
    for(i=0;i<expo_len+1;i++)
    {
        temp_expo = expo[i];
        for(j=0;j<64;j++)
        {
            if(temp_expo & 0x1UL)
                modmult1024(result,result,mod_data,key);

            modmult1024(mod_data,mod_data,mod_data,key);
            temp_expo = temp_expo >> 1;
        }
    }
    for(i=0;i<16;i++)
        res[i]=result[i];


    return 1;
}




bool addbignum(uint64_t res[], uint64_t op1[], uint64_t op2[],uint32_t n)
{
	uint32_t i;
	uint64_t j,k,carry=0;
	for(i = 0; i<n; i++)
	{
		j = (op1[i] & 0xffffffff) + (op2[i] & 0xffffffff) + carry;
		
		k = ((op1[i]>>32) & 0xffffffff) + ((op2[i]>>32) & 0xffffffff) + ((j>>32) & 0xffffffff);
				
		carry = ((k>>32) & 0xffffffff);
		
		res[i] = ((k & 0xffffffff)<<32)  | (j & 0xffffffff);
	}
	res[i] = carry;
	return 0;
} 

bool multbignum(uint64_t res[], uint64_t op1[], uint32_t op2 ,uint32_t n)
{
	uint32_t i;
	uint64_t j,k,carry1=0,carry2=0;
	for(i = 0; i<n; i++)
	{
		j = (op1[i] & 0xffffffff) * (op2 & 0xffffffff);
		
		k = ((op1[i]>>32) & 0xffffffff) * (op2 & 0xffffffff);
		carry1 = ((k>>32) & 0xffffffff);
		k = (k & 0xffffffff) + ((j>>32) & 0xffffffff);
		j = (j & 0xffffffff) + carry2;
		k = k + ((j>>32) & 0xffffffff);
		carry2 = carry1 + ((k>>32) & 0xffffffff);
		
		res[i] = ((k & 0xffffffff)<<32)  | (j & 0xffffffff);
	}
	res[i] = carry2;
	return 0;
} 
bool modmult1024(uint64_t res[], uint64_t op1[], uint64_t op2[],uint64_t mod[]) //optimized
{
    int32_t i,j;
    uint64_t mult1[33]={0},mult2[33]={0},
            result[33]={0},xmod[33]={0};

    for(i=0;i<16;i++)
        xmod[i]=mod[i];

    for(i=0;i<16;i++)
    {
        for(j=0;j<33;j++)
        {
            mult1[j]=0;
            mult2[j]=0;
        }
        multbignum(mult1,op1,(op2[i]&0xffffffff),16);
        multbignum(mult2,op1,((op2[i]>>32)&0xffffffff),16);
        slnbignum(mult2,mult2,33,32);
        addbignum(mult2,mult2,mult1,32);

        slnbignum(mult2,mult2,33,64*i);

        addbignum(result,result,mult2,32);

    }
    modbignum(result,result,xmod,33);
    for(i=0;i<16;i++)
            res[i]=result[i];

    return 0;
}
/*
bool modmult1024(uint64_t res[], uint64_t op1[], uint64_t op2[],uint64_t mod[])
{
	int32_t i,j;
	uint64_t mult1[19]={0},mult2[19]={0},result[18]={0};

	for(i=0;i<16;i++)
	{
		multbignum(mult1,op1,(op2[i]&0xffffffff),16);

		multbignum(mult2,op1,((op2[i]>>32)&0xffffffff),16);
		slnbignum(mult2,mult2,17,32);
		addbignum(mult2,mult2,mult1,17);
		modbignum(mult2,mult2,mod,17);

		for(j=0;j<i;j++)
		{
		    slnbignum(mult2,mult2,17,64);
		    modbignum(mult2,mult2,mod,17);
		}
		
		addbignum(result,result,mult2,16);
		modbignum(result,result,mod,17);
		
	}
	for(i=0;i<16;i++)
	        res[i]=result[i];
	
	return 0;
}
*/
bool modbignum(uint64_t res[],uint64_t op1[], uint64_t op2[],uint32_t n)//optimized
{
    uint32_t i;
    int32_t len_op1,len_op2,len_dif;

    len_op1 = bit_length(op1,n);
    len_op2 = bit_length(op2,n);
    len_dif = len_op1 - len_op2;



    for(i=0;i<n;i++)
        res[i]=op1[i];

    if(len_dif < 0)
    {
        return 1;
    }

    if(len_dif == 0)
    {
        while(compare(res,op2,n)>=0)
        {
            subbignum(res,res,op2,n);
        }
        return 1;
    }

    uint32_t len_diff=len_dif;
    slnbignum(op2,op2,n,len_diff);
    for(i=0;i<len_diff;i++)
    {
        srnbignum(op2,op2,n,1);
        while(compare(res,op2,n)>=0)
        {
            subbignum(res,res,op2,n);
        }
    }

    return 1;
}

/*
bool modbignum(uint64_t res[],uint64_t op1[], uint64_t op2[],uint32_t n)
{
    uint32_t i;
	int32_t len_op1,len_op2,len_dif;
	
	len_op1 = bit_length(op1,n);
	len_op2 = bit_length(op2,n);
	len_dif = len_op1 - len_op2;
	
	for(i=0;i<n;i++)
		res[i]=op1[i];
	
	if(len_dif < 0)
	{		
		return 1;
	}
	if(len_dif == 0)
	{
		modnum(res,res,op2,n);
		return 1;
	}
	
	slnbignum(op2,op2,n,len_dif);
	for(i=0;i<len_dif;i++)
	{
		srnbignum(op2,op2,n,1);
		modnum(res,res,op2,n);
	}
	return 1;
}
*/
/****************************************************************
 * bool modnum(uint64_t res[],uint64_t op1[], uint64_t op2[],uint32_t n)
 * res = op1 % op2
 * n is bit length/64
 * res must have extra 64 bits to avoid errors 
 ****************************************************************/
bool modnum(uint64_t res[],uint64_t op1[], uint64_t op2[],uint32_t n)
{
	uint32_t i;
	bool result=0;
	for(i=0;i<n;i++)
		res[i]=op1[i];
		
	while(!result)
	{
		result = subbignum(res,res,op2,n);
	}
	
	addbignum(res,res,op2,n);
	res[n]=0;
			
	return 0;
}
/****************************************************************
* int32_t compare(uint64_t op1[], uint64_t op2[],uint32_t n)
* returns 1 if op1>op2
* 		 -1 if op1<op2
* 		  0 if op1=op2
*****************************************************************/
int32_t compare(uint64_t op1[], uint64_t op2[],uint32_t n)
{
	for( ; n>0; n--)
	{
		if(op1[n-1]>op2[n-1])
		{
			return 1;
		}
		else if(op1[n-1]<op2[n-1])
		{
			return -1;
		}
	}
			
	return 0;
}

/****************************************************************
 * bool subbignum(uint64_t res[], uint64_t op1[], uint64_t op2[],uint32_t n)
 * subtracts op2 from op1
 * returns 0 if op1>=op2
 * 		   1 if op1<op2
 * result is not valid if return value is 1 (or is in 2's compliment :P)
 * **************************************************************/
bool subbignum(uint64_t res[], uint64_t op1[], uint64_t op2[],uint32_t n)
{
	bool carry=0;
	uint32_t i;
	for(i=0;i<n;i++)
	{
		if(carry)
		{
			if(op1[i]!=0)
				carry=0;
			op1[i]--;		
		}
		if(op1[i]<op2[i])
			carry = 1;
			
		res[i]= op1[i] - op2[i];
	}	
	return carry;
}
bool slnbignum(uint64_t res[], uint64_t op[],uint32_t len, uint32_t n)//shift left by n
{
    uint32_t i,x,y;
    uint64_t j,k,carry = 0;
    x = n / 64;
    y = n % 64;

    for(i=len; i - x >0; i--)
    {
        res[i-1] = op[i - 1 - x];
    }
    for(;i>0;i--)
    {
        res[i-1] = 0;
    }
    for(i=0;i<len;i++)
    {
        j = res[i];
        k=0;
        for(x=0;x<y;x++)
        {
            if(j & 0x8000000000000000)
            {
                k = (k<<1) | 1;
            }
            else
            {
                k = (k<<1);
            }
            j = j <<1;
        }
        res[i] = j | carry;
        carry = k;
    }
    return 1;
}
bool srnbignum(uint64_t res[], uint64_t op[],uint32_t len, uint32_t n)//shift right by n
{
    uint32_t i,x,y;
    uint64_t j,k,carry = 0;
    x = n / 64;
    y = n % 64;

    for(i=0; i + x < len; i++)
    {
        res[i] = op[i + x];
    }
    for(;i<len;i++)
    {
        res[i] = 0;
    }
    for(i=len;i>0;i--)
    {
        j = res[i-1];
        k=0;
        for(x=0;x<y;x++)
        {
            if(j & 0x0000000000000001)
            {
                k = (k>>1) | 0x8000000000000000;
            }
            else
            {
                k = (k>>1);
            }
            j = j >>1;
        }
        res[i-1] = j | carry;
        carry = k;
    }
    return 1;

}
/****************************************************************
 * uint32_t bit_length(uint64_t op[],uint32_t n)
 * returns position of MSB present
 *
 *
 ****************************************************************/
uint32_t bit_length(uint64_t op[],uint32_t n)
{
    uint32_t len=0;
    uint32_t i;
    uint64_t unit = 1;
    for( ;n>0;n--)
    {
        if(op[n-1]==0)
            continue;
        for(i=64;i>0;i--)
        {
            if(op[n-1] & (unit<<(i-1)))
            {
                len = (64*(n-1)) + i;
                break;
            }

        }
        if(len)
            break;
    }
    return len;
}

void temp_disp(uint64_t x[], uint32_t n)
{
	for( ; n>0 ; n--)
	{
		printf("%016lx",x[n-1]);
	}
	printf("\n");
	return;
}


static void* alloc_mem (int align, int size)
{
	void* a;
	int size2 = size + align;

	VERBOSE2 ("%s Enter Align: %d Size: %d\n", __func__, align, size);

	if (posix_memalign ((void**)&a, 4096, size2) != 0) {
		perror ("FAILED: posix_memalign()");
		return NULL;
	}

	VERBOSE2 ("%s Exit %p\n", __func__, a);
	return a;
}

static void free_mem (void* a)
{
	VERBOSE2 ("Free Mem %p\n", a);

	if (a) {
		free (a);
	}
}


static void usage (const char* prog)
{
	VERBOSE0 ("SNAP String Match (Regular Expression Match) Tool.\n");
	VERBOSE0 ("Usage: %s\n"
			  "	-h, --help		prints usage information\n"
			  "	-v, --verbose		verbose mode\n"
			  "	-C, --card <cardno>     card to be used for operation\n"
			  "	-V, --version\n"
//			  "	-q, --quiet		quiece output\n"
			  "	-t, --timeout		Timeout after N sec (default 1 sec)\n"
			  "	-I, --irq		Enable Action Done Interrupt (default No Interrupts)\n"
			  , prog);
}

int main (int argc, char* argv[])
{
	char device[64];
//	struct snap_card* dn;   /* lib snap handle */
	int card_no = 0;
	int cmd;
	int rc = 1;
//	int patt_size = 4096*10;
//	void* patt_src_base = alloc_mem(64, patt_size);
//	void* patt_tgt_base = alloc_mem(64, patt_size);

//	int timeout = ACTION_WAIT_TIME;
//	snap_action_flag_t attach_flags = 0;
	int memory_size = 4096*10;
	void* patt_src_base = alloc_mem(64,memory_size);
	void* patt_tgt_base = alloc_mem(64,memory_size);
	





	while (1) {
		int option_index = 0;
		static struct option long_options[] = {
			{ "card",	 required_argument, NULL, 'C' },
			{ "verbose",     no_argument,	    NULL, 'v' },
			{ "help",	 no_argument,	    NULL, 'h' },
			{ "version",     no_argument,	    NULL, 'V' },
			{ "quiet",       no_argument,	    NULL, 'q' },
			{ "timeout",     required_argument, NULL, 't' },
			{ "irq",	  no_argument,	   NULL, 'I' },
			{ 0,		  no_argument,	   NULL, 0   },
		};
		cmd = getopt_long (argc, argv, "C:t:IqvVh",
						   long_options, &option_index);

		if (cmd == -1) { /* all params processed ? */
			break;
		}

		switch (cmd) {
		case 'v':   /* verbose */
			verbose_level++;
			break;

		case 'V':   /* version */
			VERBOSE0 ("%s\n", version);
			exit (EXIT_SUCCESS);;

		case 'h':   /* help */
			usage (argv[0]);
			exit (EXIT_SUCCESS);;

		case 'C':   /* card */
			card_no = strtol (optarg, (char**)NULL, 0);
			break;

		case 't':
			//timeout = strtol (optarg, (char**)NULL, 0); /* in sec */
			break;

		case 'I':	  /* irq */
			//attach_flags = SNAP_ACTION_DONE_IRQ | SNAP_ATTACH_IRQ;
			break;

		default:
			usage (argv[0]);
			exit (EXIT_FAILURE);
		}
		
	}  // while(1)

	VERBOSE2 ("Open Card: %d\n", card_no);
	sprintf (device, "/dev/cxl/afu%d.0s", card_no);
	

	int i;
//	uint64_t data[16]={0xbcd8b9115b57c68f,0x90c2ed9762842e21,0x994cb02de5759f87,0x3823ada474db165a,	
//                           0x2939d8ad21cb9c7b,0xbc99c2835e0d7cd6,0xc529d2d071f6a542,0xc9e05c5ce2a3919b,		
//			   0x1a2d60140b7c0afd,0x545fc7c10cebe959,0x2351f03e958fcff6,0x43cc08f45862cce9,
//                           0x496a46b65a72b40c,0x38f0c082d72ef99e,0x972de6eea9b9e0da,0x9daae3d132d9eaf9};
	char msg[150] = {0};
	clock_t start_enc,stop_enc,start_dec,stop_dec;
	unsigned long us_enc=0,us_dec = 0;
	strcpy(msg,"hello, this is first rsa encode.");
//	for(i=0;i<16;i++)
//	{
//	    x[i] = (uint64_t)rand()*(uint64_t)rand();
//	    y[i] = (uint64_t)rand()*(uint64_t)rand();
//	}
	for(i=0;i<8;i++)
	{
	    uint8_t temp=data[i];
	    data[i]=data[15-i];
	    data[15-i]=temp;
	}
	for(i=0;i<8;i++)
	{
	    uint8_t temp=key[i];
	    key[i]=key[15-i];
	    key[15-i]=temp;
	}
	for(i=0;i<8;i++)
	{
	    uint8_t temp=mod[i];
	    mod[i]=mod[15-i];
	    mod[15-i]=temp;
	}
	//temp_disp(msg,18);
	//temp_disp(data,18);
	e[0] = 0x10001;
	//temp_disp(e,18);
	//encryption
	start_enc = clock();
	for(i=0;i<10;i++)
	    rsa1024(z,x,e,mod);
	stop_enc = clock();
	//decryption
    start_dec = clock();
    for(i=0;i<10;i++)
        rsa1024(z,data,key,mod);
    stop_dec = clock();
	uint_64 *p;
	p=z;
	VERBOSE0 ("%lx\n",*p++);

	//temp_disp(z,18);
    us_enc = (stop_enc - start_enc)/10 ;
    us_dec = (stop_dec - start_dec)/10 ;
//	printf("Avg time taken for 1024 bit rsa encryption is %ld ms\n",us_enc/1000);
	printf("Avg time taken for 1024 bit rsa decryption is %ld ms\n",us_dec/1000);


//__exit1:
	// Unmap AFU MMIO registers, if previously mapped
	//VERBOSE2 ("Free Card Handle: %p\n", dn);
	//snap_card_free (dn);

	free_mem(patt_src_base);
	free_mem(patt_tgt_base);

	VERBOSE1 ("End of Test rc: %d\n", rc);
	return rc;
} // main end
