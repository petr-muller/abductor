#include <stdlib.h>
int nondet;
#define NONDET (&nondet > 0)


typedef void VOID;
typedef void *PVOID;

typedef struct InnerStruct {
  struct InnerStruct *NextIS;
  int                 Size;
} InnerStruct, *PInnerStruct;

typedef struct OuterStruct {
  struct OuterStruct *NextOS;
  PInnerStruct        pInnSt;
} OuterStruct, *POuterStruct;

typedef struct {
  POuterStruct NextOS;
} HEADER, *PHEADER;


VOID FreeInnSt_recursive(PInnerStruct InnSt) 
{
  if(InnSt)
    {
       FreeInnSt_recursive(InnSt->NextIS);
      free(InnSt);
    }
}

VOID delete_nested_list(PHEADER header_node) {

  PHEADER head;
  head = header_node;
  while ((PHEADER)(head->NextOS) != head) {

    PVOID           buffer;
    POuterStruct      OutSt;
    PInnerStruct pInnSt;

    head = header_node;
    OutSt = head->NextOS;
    head->NextOS = OutSt->NextOS;

    if (OutSt)
      {    
	pInnSt = OutSt->pInnSt;
	if (pInnSt)
	   FreeInnSt_recursive(pInnSt);    
	free(OutSt);
      }
  }
}

VOID TraverseInnSt_recursive(PInnerStruct InnSt) 
{
  if(InnSt)
    {
       TraverseInnSt_recursive(InnSt->NextIS);
    }
}


VOID traverse_nested_list(PHEADER header_node) {

  PHEADER head;
  head = header_node;
  while ((PHEADER)(head->NextOS) != head) {

    PVOID           buffer;
    POuterStruct      OutSt;
    PInnerStruct pInnSt;

    head = header_node;
    OutSt = head->NextOS;
    head->NextOS = OutSt->NextOS;

    if (OutSt)
      {    
	pInnSt = OutSt->pInnSt;
	if (pInnSt)
	   TraverseInnSt_recursive(pInnSt);
      }
  }
}

VOID InsertInnSt(PInnerStruct InnSt) 
{
  PInnerStruct tmp;

  if(InnSt)
    {
      if(NONDET) {
	tmp = InnSt->NextIS;
	InnSt->NextIS = mallocnonnull(sizeof(InnerStruct));
	InnSt->NextIS->NextIS = tmp;
	InsertInnSt(tmp);
      }
      else  TraverseInnSt_recursive(InnSt->NextIS);
    }
}


VOID some_insert(PHEADER header_node) {

  PHEADER head;
  head = header_node;
  while ((PHEADER)(head->NextOS) != head) {

    PVOID           buffer;
    POuterStruct      OutSt;
    PInnerStruct pInnSt;

    head = header_node;
    OutSt = head->NextOS;
    head->NextOS = OutSt->NextOS;

    if (OutSt)
      {    
	pInnSt = OutSt->pInnSt;
	if (pInnSt)
	   InsertInnSt(pInnSt);
      }
  }
}

