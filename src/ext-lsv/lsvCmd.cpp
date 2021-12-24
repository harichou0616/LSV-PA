#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include "sat/cnf/cnf.h"
using namespace std;
extern "C" Aig_Man_t *Abc_NtkToDar(Abc_Ntk_t *pNtk, int fExors, int fRegisters);
static int lsv_or_bidec(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_CommandPrintMsfc(Abc_Frame_t* pAbc, int argc, char** argv);
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_msfc", Lsv_CommandPrintMsfc, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_or_bidec", lsv_or_bidec, 0);
}
void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}
int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}


class NODE{
  public:
    NODE(Abc_Obj_t* pObj):pObj(pObj){
      ObjId = Abc_ObjId(pObj);
      ObjName = Abc_ObjName(pObj);
    }
    NODE(Abc_Obj_t* pObj,unsigned int ObjId,char* ObjName):pObj(pObj),ObjId(ObjId),ObjName(ObjName){}
    Abc_Obj_t* getObj(){
      return pObj;
    }
    unsigned int getObjId(){
      return ObjId;
    }
    char* getObjName(){
      return ObjName;
    }
  private:
    Abc_Obj_t* pObj;
    unsigned int ObjId;
    char* ObjName;
};

void Traversal(vector<NODE*> &msfc_list, Abc_Obj_t* pObj)
{
  Abc_Obj_t* pFanin;
  int i;
  Abc_ObjForEachFanin(pObj, pFanin, i) {
    if((Abc_ObjFanoutNum(pFanin)==1)&&(Abc_ObjIsPi(pFanin) == 0)){
      msfc_list.push_back(new NODE(pFanin));
      Traversal(msfc_list, pFanin);
    }
  }
}
bool compare_list(NODE* node1, NODE* node2){
  return Abc_ObjId(node1->getObj()) < Abc_ObjId(node2->getObj());
}
bool compare_ALLSTAR(vector<NODE*> list1, vector<NODE*> list2){
  return Abc_ObjId(list1[0]->getObj()) < Abc_ObjId(list2[0]->getObj());
}
void push_back_ALLSTAR(vector<vector<NODE*>> &MSFC_ALLSTAR, vector<NODE*> &msfc_list, Abc_Obj_t* pObj){
  msfc_list.push_back(new NODE(pObj));
  Traversal(msfc_list, pObj);
  sort(msfc_list.begin(),msfc_list.end(), compare_list);
  MSFC_ALLSTAR.push_back(msfc_list);
}

void myfile_ALLSTAR(vector<vector<NODE*>> &MSFC_ALLSTAR){
  std::ofstream myfile;
  //myfile.open("example.txt");
  int MSFC_i = 0;
  vector<vector<NODE*>>::iterator it;
  //myfile << "ABC command line: \"lsv_print_msfc\"." << endl << endl;
  for(it=MSFC_ALLSTAR.begin();it!=MSFC_ALLSTAR.end();++it){
    //myfile << "MSFC " << MSFC_i <<": ";
    cout << "MSFC " << MSFC_i <<": ";
    int dotFlag = 0;
    vector<NODE*>::iterator it2;    
    for(it2=(*it).begin();it2!=(*it).end();++it2){
      if(dotFlag == 0) dotFlag = 1;
      else cout << ",";//myfile << "," ;
      //myfile<< Abc_ObjName((*it2)->getObj()) ;
      cout << Abc_ObjName((*it2)->getObj()) ;
    }
    //myfile << endl;
    cout << endl;
    MSFC_i++;
  }
  //myfile.close();
}

void Lsv_NtkPrintMsfc(Abc_Ntk_t* pNtk) {
  vector<vector<NODE*>> MSFC_ALLSTAR;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachObj(pNtk, pObj, i) {
    vector<NODE*> msfc_list;
    Abc_Obj_t* pFanout;
    int j;
    if(Abc_ObjIsNode(pObj)|| Abc_ObjType(pObj) == ABC_OBJ_CONST1){
      if(Abc_ObjFanoutNum(pObj)>1) push_back_ALLSTAR(MSFC_ALLSTAR,msfc_list,pObj);
      else{
        Abc_ObjForEachFanout(pObj,pFanout,j){
	        if(Abc_ObjIsPo(pFanout))push_back_ALLSTAR(MSFC_ALLSTAR,msfc_list,pObj);
        }
      }
    }
  }
  sort(MSFC_ALLSTAR.begin(),MSFC_ALLSTAR.end(),compare_ALLSTAR);
  myfile_ALLSTAR(MSFC_ALLSTAR);
}


int Lsv_CommandPrintMsfc(Abc_Frame_t* pAbc, int argc, char** argv) {
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
  Lsv_NtkPrintMsfc(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}


void printout(bool xflag, int btar, int cresua, int dnfina, const std::vector<int>& xvector,const std::vector<int>& yvector,sat_solver *solver){
  xflag=true; int counter1 = 0;int counter2 = 0;
  std::vector<int>roots;
  btar=xvector.size();
  int *pFinal;
  lit *aption = new lit[xvector.size()*2];

  for (int i=0;i<btar;i++){
    roots.push_back(0);
    counter1++;
  }
  counter1 = 0;
    for(int i=0;i<roots.size();i++){
      counter1++;
      for(int j=i+1;j<roots.size();j++){
        counter2++;
        roots[i]=1;
        roots[j]=2;
        for(int q=0;q<roots.size();q++){
          switch (roots[q])
          {
          case 0:
            aption[q]=toLitCond(xvector[q],1);
            aption[q+roots.size()]=toLitCond(yvector[q],1);
            break;
          case 1:
            aption[q]=toLitCond(xvector[q],1);
            aption[q+roots.size()]=toLitCond(yvector[q],0);
            break;
          case 2:
            aption[q]=toLitCond(xvector[q],0);
            aption[q+roots.size()]=toLitCond(yvector[q],1);
            break;
          }
        }
        cresua=sat_solver_solve(solver,aption,aption+xvector.size()*2,0,0,0,0);
        if(cresua!=l_True){
          printf("1\n");
          dnfina=sat_solver_final(solver,&pFinal); 
          std::vector<int>ans;
          for (int e=0;e<xvector.size();e++){
            ans.push_back(3);
          }
          for (int e=0;e<dnfina;e++){
            for(int r=0;r<xvector.size();r++){
              if(xvector[r]==pFinal[e]/2){
                ans[r]^=1;
                break;
              }else if(yvector[r]==pFinal[e]/2){
                ans[r]^=2;
                break;
              }
            }
          }
          for(int e=0;e<ans.size();e++){
            if(ans[e]!=3){
              printf("%d",ans[e]);
            }else{
              printf("1");
            }
          }
          printf("\n");
          xflag=false;
          break;
        }
        roots[i]=0;
        roots[j]=0;
      }
      if(!xflag)break;
    }
    if(xflag)printf("0\n");
}
void lsv_print_ORbid(Abc_Ntk_t*  pNtk){
  
  Abc_Obj_t* pObj;Aig_Obj_t* pObj2;
  Cnf_Dat_t *C1; Cnf_Dat_t *C2;  Cnf_Dat_t *C3;
  Abc_Ntk_t * abcntk;
  Aig_Man_t *aigman;
  sat_solver *sol1;sat_solver *sol2;sat_solver *sol3;
  int i,j;
  Abc_NtkForEachPo(pNtk, pObj, i){
    printf("PO %s support partition: ",Abc_ObjName(pObj));
    std::vector<int> fvector; std::vector<int> xvector; std::vector<int> yvector;    
    abcntk=Abc_NtkCreateCone(pNtk,Abc_ObjFanin0(pObj),Abc_ObjName(pObj),0);
    if (Abc_ObjFaninC0(pObj)) Abc_NtkPo(abcntk, 0)->fCompl0 ^= 1;
    aigman = Abc_NtkToDar(abcntk, 0, 0);
    C1 = Cnf_Derive(aigman, 0); 
    C2 = Cnf_DataDup(C1);
    Cnf_DataLift(C2,C2->nVars);
    C2->pClauses[C2->nClauses-1][0]=C2->pClauses[C2->nClauses-1][0]^1;  
    C3 = Cnf_DataDup(C2);
    Cnf_DataLift(C3,C2->nVars);
    Aig_ManForEachCi(aigman,pObj2,j){
      fvector.push_back(C1->pVarNums[pObj2->Id]);
    }
    assert(Aig_ManCoNum(aigman)==1);
    assert(C2->nVars==C3->nVars);
    sol1 = (sat_solver *)Cnf_DataWriteIntoSolver(C1, 1, 0);
    sol2 = (sat_solver *)Cnf_DataWriteIntoSolverInt(sol1, C2, 1, 0);
    sol3 = (sat_solver *)Cnf_DataWriteIntoSolverInt(sol2, C3, 1, 0);
    if(sol1==0 || sol2==0){
      printf("0\n");
      continue;
    }
    for(int k=0;k<fvector.size();k++){
      xvector.push_back(sat_solver_addvar(sol3));
      yvector.push_back(sat_solver_addvar(sol3));
      lit * L_array1 = new lit [3];
      lit * L_array2 = new lit [3];
      lit * L_array3 = new lit [3];
      lit * L_array4 = new lit [3];
      int *aa = new int[2];
      int *ba = new int[2];

      L_array1[0] = toLitCond( fvector[k], 0 );
      L_array2[0] = toLitCond( fvector[k], 1 );
      L_array3[0] = toLitCond( fvector[k], 0 );
      L_array4[0] = toLitCond( fvector[k], 1 );
      L_array1[1] = toLitCond( fvector[k]+C2->nVars, 1 );
      L_array2[1] = toLitCond( fvector[k]+C2->nVars, 0 );
      L_array3[1] = toLitCond( fvector[k]+2*C2->nVars, 1 );
      L_array4[1] = toLitCond( fvector[k]+2*C2->nVars, 0 );
      L_array1[2] = toLitCond( xvector[k], 0 );
      L_array2[2] = toLitCond( xvector[k], 0 );
      L_array3[2] = toLitCond( yvector[k], 0 );
      L_array4[2] = toLitCond( yvector[k], 0 );
      aa[0] = sat_solver_addclause( sol3, L_array1, L_array1 + 3 );
      aa[1] = sat_solver_addclause( sol3, L_array2, L_array2 + 3 );
      ba[0] = sat_solver_addclause( sol3, L_array3, L_array3 + 3 );
      ba[1] = sat_solver_addclause( sol3, L_array4, L_array4 + 3 );
      assert( !(fvector[k] < 0) & !(fvector[k]+C2->nVars < 0) & !(xvector[k] < 0) );
      assert( aa[0] );
      assert( aa[1] );
      assert( !(fvector[k] < 0) & !(fvector[k]+2*C2->nVars < 0) & !(yvector[k] < 0) );
      assert( ba[0] );
      assert( ba[1] );
    }
    bool flag = false;
    int array[3] = {0};
    printout(flag, array[0],array[1],array[2], xvector,yvector,sol3);
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