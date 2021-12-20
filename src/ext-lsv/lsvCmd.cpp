#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/cnf/cnf.h"
#include<algorithm>
#include <vector>
extern "C" Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
static int lsv_or_bidec(Abc_Frame_t* pAbc, int argc, char** argv);

void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_or_bidec", lsv_or_bidec, 0);
}
void destroy(Abc_Frame_t* pAbc) {}
Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;


void buff( sat_solver * pSat, int iA, int iB, int iV, int Comp )
{
    lit * L_array1 = new lit [3];
    lit * L_array2 = new lit [3];
    int *a = new int[2];
    L_array1[0] = toLitCond( iA, 0 );
    L_array2[0] = toLitCond( iA, 1 );
    L_array1[1] = toLitCond( iB, !Comp );
    L_array2[1] = toLitCond( iB, Comp );
    L_array1[2] = toLitCond( iV, 0 );
    L_array2[2] = toLitCond( iV, 0 );
    a[0] = sat_solver_addclause( pSat, L_array1, L_array1 + 3 );
    a[1] = sat_solver_addclause( pSat, L_array2, L_array2 + 3 );
    assert( !(iA < 0) & !(iB < 0) & !(iV < 0) );
    assert( a[0] );
    assert( a[1] );
}


void lsv_print_ORbid(Abc_Ntk_t*  pNtk){
  
  Abc_Obj_t* pObj;Aig_Obj_t* pObj2;
  Cnf_Dat_t *C1; Cnf_Dat_t *C2;  Cnf_Dat_t *C3;
  Abc_Ntk_t * abcntk;
  Aig_Man_t *aigman;
  sat_solver *sol1;sat_solver *sol2;sat_solver *sol3;
  int counter[3];
  int i,j;
  counter[3]=0;
  Abc_NtkForEachPo(pNtk, pObj, i){
    std::vector<int> f; std::vector<int> a; std::vector<int> b;
    counter[3]++;
    
    abcntk=Abc_NtkCreateCone(pNtk,Abc_ObjFanin0(pObj),Abc_ObjName(pObj),0);
    if (Abc_ObjFaninC0(pObj)) Abc_NtkPo(abcntk, 0)->fCompl0 ^= 1;
    printf("PO %s support partition: ",Abc_ObjName(pObj));
    
    aigman = Abc_NtkToDar(abcntk, 0, 0);
    C1 = Cnf_Derive(aigman, 0); 
    C2 = Cnf_DataDup(C1);
    Cnf_DataLift(C2,C2->nVars);
    C2->pClauses[C2->nClauses-1][0]=C2->pClauses[C2->nClauses-1][0]^1;  
    C3 = Cnf_DataDup(C2);
    Cnf_DataLift(C3,C2->nVars);
    Aig_ManForEachCi(aigman,pObj2,j){
      f.push_back(C1->pVarNums[pObj2->Id]);
    }
    assert(Aig_ManCoNum(aigman)==1);
    assert(C2->nVars==C3->nVars);
    sol1 = (sat_solver *)Cnf_DataWriteIntoSolver(C1, 1, 0);
    sol2 = (sat_solver *)Cnf_DataWriteIntoSolverInt(sol1, C2, 1, 0);
    sol3 = (sat_solver *)Cnf_DataWriteIntoSolverInt(sol2, C3, 1, 0);

    for(int k=0;k<f.size();k++){
      a.push_back(sat_solver_addvar(sol3));
      b.push_back(sat_solver_addvar(sol3));

      lit * L_array1 = new lit [3];
      lit * L_array2 = new lit [3];
      lit * L_array3 = new lit [3];
      lit * L_array4 = new lit [3];
      int *aa = new int[2];
      int *ba = new int[2];

      L_array1[0] = toLitCond( f[k], 0 );
      L_array2[0] = toLitCond( f[k], 1 );
      L_array3[0] = toLitCond( f[k], 0 );
      L_array4[0] = toLitCond( f[k], 1 );
      L_array1[1] = toLitCond( f[k]+C2->nVars, 1 );
      L_array2[1] = toLitCond( f[k]+C2->nVars, 0 );
      L_array3[1] = toLitCond( f[k]+2*C2->nVars, 1 );
      L_array4[1] = toLitCond( f[k]+2*C2->nVars, 0 );
      L_array1[2] = toLitCond( a[k], 0 );
      L_array2[2] = toLitCond( a[k], 0 );
      L_array3[2] = toLitCond( b[k], 0 );
      L_array4[2] = toLitCond( b[k], 0 );
      aa[0] = sat_solver_addclause( sol3, L_array1, L_array1 + 3 );
      aa[1] = sat_solver_addclause( sol3, L_array2, L_array2 + 3 );
      ba[0] = sat_solver_addclause( sol3, L_array3, L_array3 + 3 );
      ba[1] = sat_solver_addclause( sol3, L_array4, L_array4 + 3 );
      assert( !(f[k] < 0) & !(f[k]+C2->nVars < 0) & !(a[k] < 0) );
      assert( aa[0] );
      assert( aa[1] );
      assert( !(f[k] < 0) & !(f[k]+2*C2->nVars < 0) & !(b[k] < 0) );
      assert( ba[0] );
      assert( ba[1] );
    }
    if(!sol1){
      printf("0\n");
      continue;
    }
    if(!sol2){
      printf("0\n");
      continue;
    }
    int flag=0;
    int *i_array = new int[3];
    int *pointer;
    i_array[0]=a.size();
    lit *aption = new lit[a.size()*2];
    int *sd = new int[i_array[0]]
    int size=  sizeof(sd)
    for(int i=0;i<size;i++){
      for(int j=i+1;j<size;j++){
        sd[i]=1; sd[j]=2;
        for(int i=0;i<size;i++){
          switch (sd[i]){
          case 0:
            aption[i]=toLitCond(a[i],1);
            aption[i+size]=toLitCond(b[i],1);
            break;
          case 1:
            aption[i]=toLitCond(a[i],1);
            aption[i+size]=toLitCond(b[i],0);
            break;
          case 2:
            aption[i]=toLitCond(a[i],0);
            aption[i+size]=toLitCond(b[i],1);
            break;
          }
        }
        i_array[1]=sat_solver_solve(sol3,aption,aption+a.size()*2,0,0,0,0);
        if(i_array[1]!=l_True){
          i_array[2]=sat_solver_final(sol3,&pointer); 
          std::vector<int>an;
          printf("1\n");
          for (int i=0; i<a.size();i++)an.push_back(3);
          for (int i=0; i<i_array[2];i++){
            for(int j=0;j<a.size();j++){
              if(a[j]==pointer[i]/2){
                an[j]= an[j] ^ 1;
                break;
              }
              else if(b[j]==pointer[i]/2){
                an[j] = an[j] ^ 2;
                break;
              }
            }
          }
          for(int i=0;i <an.size();i++){
            if(an[i]!=3)printf("%d",an[i]);
            else printf("1");
          }
          flag=1;
          printf("\n");
          break;
        }
          sd[i]=0;
          sd[j]=0;
      }
        if(flag==1)break;
    }
    if(flag==0)printf("0\n");  
  }
}











int lsv_or_bidec(Abc_Frame_t* pAbc, int argc, char** argv){
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  lsv_print_ORbid(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_or_bidec [-h]\n");
  Abc_Print(-2, "\t      find OR bi-decomposable under a variable partition \n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}