#include <time.h>
#include <stdio.h>
#include <iostream>
#include <cstdlib>
#include "util.h"
#include <errno.h>
#include <unistd.h>
#include <pthread.h>
#include <vector>
#include <list>
#include <string>
#include <algorithm>
#include "minisat/core/SolverTypes.h"
#include "minisat/core/Solver.h"
using namespace std;
#define Wait_Time 5000
#define handle_error(msg) \
        do { perror(msg); exit(EXIT_FAILURE); } while (0)

#define handle_error_en(en, msg) \
        do { errno = en; perror(msg); exit(EXIT_FAILURE); } while 

//Enums Used
enum Result 
{
    NOT_FOUND,
    FOUND
};
enum STATUS 
{
    WAITING_FOR_VERTEX,
    WAITING_FOR_EDGES,
    GO_CALCULATE,
    DONE_CALCULATING,
};
bool Value_not_Contained(int val,int val2, vector<int> *v);
bool All_Threads_finished();
static void save_thread_timer( clockid_t cid , timespec *ts);
string trim(const string& str);
void init_edge_vector(int vertex_num, int old_vertex_num);
void command_parser(string input);
void edge_command(string input, size_t space);
void vertex_command(string input, size_t space);
int edge_number_calc(string input, size_t space);
void Vertex_Cover_Printer(char *msg, vector<int> *v); 

string input;
int vertex_num = 0; //i to n
int edge_number = 0; // Captured edges

 vector<int> vertex_cover_CNF_SAT_VC;
 vector<int> vertex_cover_VC_1;
 vector<int> vertex_cover_VC_2;  

 int **edges = NULL;
int **edges_VC_1 = NULL;
int status_flag = WAITING_FOR_VERTEX;
int eof_flag=0;

pthread_t thread_Parser;
pthread_t thread_CNF_SAT_VC;
pthread_t thread_APPROX_VC_1;
pthread_t thread_APPROX_VC_2;

auto lock_Parser = new TryLock();
auto lock_CNF_SAT_VC = new TryLock();
auto lock_APPROX_VC_1= new TryLock();
auto lock_APPROX_VC_2= new TryLock();

struct timespec TS_CNF_SAT_VC;
struct timespec TS_APPROX_VC_1;
struct timespec TS_APPROX_VC_2;

clockid_t TL_CNF_SAT_VC;
clockid_t TL_APPROX_VC_1;
clockid_t TL_APPROX_VC_2;



void* Parser(void* unused)
{   
   while (std::getline(cin, input))
    {
        
        input=trim(input);
        command_parser(input);
        input = "";
        if(status_flag == GO_CALCULATE)
        { 
            lock_CNF_SAT_VC->tryAcquire();
            lock_APPROX_VC_1->tryAcquire();
            lock_APPROX_VC_2->tryAcquire();
            status_flag = DONE_CALCULATING;

                lock_Parser->release();
                while (!All_Threads_finished()){/*wait*/}
                //cout<< "ST , " << (TS_CNF_SAT_VC.tv_sec*1000000000) + (TS_CNF_SAT_VC.tv_nsec)<< ",";
                //cout<< "VC_1 , "<< (TS_APPROX_VC_1.tv_sec*1000000000) + (TS_APPROX_VC_1.tv_nsec)<<",";
                //cout<< "VC_2 , "<< (TS_APPROX_VC_2.tv_sec*1000000000) + (TS_APPROX_VC_2.tv_nsec)<< endl;
                Vertex_Cover_Printer("CNF-SAT-VC:", &vertex_cover_CNF_SAT_VC);
                Vertex_Cover_Printer("APPROX-VC-1:", &vertex_cover_VC_1);
                Vertex_Cover_Printer("APPROX-VC-2:", &vertex_cover_VC_2);
                vertex_cover_CNF_SAT_VC.clear();
                vertex_cover_VC_1.clear();
                vertex_cover_VC_2.clear();
                break;
        }
   }
   if (!cin)
   {
        if (cin.eof()) 
        {
            eof_flag=1;
        }
   }  
    
    return 0;
}

void* CNF_SAT_VC(void* unused)
{
    pthread_getcpuclockid(pthread_self(), &TL_CNF_SAT_VC);
    while (lock_Parser->isHeld() == true) { /* wait */ }
    
    status_flag = DONE_CALCULATING;
           bool exit_flag = false;
           int last_result = NOT_FOUND;
           int k_solver = vertex_num/2; // j to k
           int last_k=vertex_num;
           int upper_bound = vertex_num-1;
           int lower_bound = 0;
            while(exit_flag == false)
            {   
                
                // Exit search routine
                if(last_k==k_solver)
                {
                    if(last_result == NOT_FOUND){k_solver+=1;exit_flag = true;}
                    else if(last_result == FOUND){exit_flag = true;}
                    #ifdef DEBUG_MODE
                    std::cout<<"LAST K: "<<k_solver<<endl;
                    #endif
                }
                last_k=k_solver;

                Minisat::Solver solver;
                Minisat::Var Matrix[vertex_num][k_solver];

                // Init variables for MiniSAT
                for (int n = 0; n < vertex_num; ++n) 
                {
                    for (int i = 0; i < k_solver; ++i) 
                    {
                        Matrix[n][i] = solver.newVar();
                    }
                }

                // Clause 1
                for(int k=0;k<k_solver;k++)
                {
                    Minisat::vec<Minisat::Lit> literals;
                    for(int i=0;i<vertex_num;i++)
                    {
                        literals.push(Minisat::mkLit(Matrix[i][k]));
                        #ifdef DEBUG_MODE
                        cout<<"X"<<"["<<i<<","<<k<<"]"<<" V ";
                        #endif
                    }
                    solver.addClause(literals);
                    literals.clear();
                    #ifdef DEBUG_MODE
                    cout<<endl;
                    #endif 
                }

                #ifdef DEBUG_MODE
                cout<<endl;
                #endif

                // Clause 2
                for(int i=0;i<vertex_num;i++)
                {    
                    for(int k=0;k<k_solver-1;k++)
                    {   Minisat::vec<Minisat::Lit> literals;
                        literals.push(~Minisat::mkLit(Matrix[i][k]));
                        literals.push(~Minisat::mkLit(Matrix[i][k+1]));
                        solver.addClause(literals);
                        literals.clear();
                        #ifdef DEBUG_MODE
                        cout<<"~X"<<"["<<i<<","<<k<<"]"<<" V "<<"~X"<<"["<<i<<","<<k+1<<"]"<<" V "<<endl;
                        #endif
                    }
                }

                #ifdef DEBUG_MODE
                cout<<endl;
                #endif

                // Clause 3
                for(int k=0;k<k_solver;k++)
                {
                    for(int i=0;i<vertex_num-1;i++)
                    {
                        for(int j=i+1;j<vertex_num;j++)
                        {
                        Minisat::vec<Minisat::Lit> literals;
                        literals.push(~Minisat::mkLit(Matrix[i][k]));
                        literals.push(~Minisat::mkLit(Matrix[j][k]));
                        solver.addClause(literals);
                        literals.clear();
                        #ifdef DEBUG_MODE
                        cout<<"~X"<<"["<<i<<","<<k<<"]"<<" V "<<"~X"<<"["<<j<<","<<k<<"]"<<" V "<<endl;
                        #endif
                        }
                    }
                } 

                #ifdef DEBUG_MODE
                cout<<endl;
                #endif

                // Clause 4
                for (int i = 0; i < edge_number; i++) 
                { 
                    Minisat::vec<Minisat::Lit> literals;
                    for (int j = 0; j < 2; j++)
                    {
                        for(int k=0;k<k_solver;k++)
                        {
                        literals.push(Minisat::mkLit(Matrix[edges[i][j]][k]));
                        #ifdef DEBUG_MODE
                        cout<<"X"<<"["<<edges[i][j]<<","<<k<<"]"<<" V ";
                        #endif
                        }
                    }
                    solver.addClause(literals);
                    literals.clear();
                    #ifdef DEBUG_MODE
                    cout<<endl;
                    #endif
                } 

               // Check for solution and retrieve model if found
               auto sat = solver.solve();

               // Solution found
               if (sat) 
               {

                  vertex_cover_CNF_SAT_VC.clear();
                    for (int n = 0; n < vertex_num; ++n) 
                    {
                        for (int i = 0; i < k_solver; ++i) 
                        {
                            if (solver.modelValue(Matrix[n][i]) == Minisat::l_True) 
                            {   

                                vertex_cover_CNF_SAT_VC.push_back(n);
                                #ifdef DEBUG_MODE
                                std::cout<<"n: "<<n<<endl;    
                                std::cout<<"i: "<<i<<endl; 
                                #endif
                            }
                        }
                    }

                    last_result = FOUND;

                    upper_bound = k_solver-1;
               }
               // Solution not found
               else 
               {  last_result = NOT_FOUND;
                  lower_bound = k_solver+1;

               }
               k_solver=(lower_bound+upper_bound)/2;  

            }


    save_thread_timer(TL_CNF_SAT_VC,&TS_CNF_SAT_VC);
    lock_CNF_SAT_VC->release();
    return 0;
}

void* APPROX_VC_1(void* unused)
{
    pthread_getcpuclockid(pthread_self(), &TL_APPROX_VC_1);
    while (lock_Parser->isHeld() == true) { /* wait */ }
    
    int exit_flag=0;
    while(!exit_flag){
        list<int> Incidents_found;
        for(int i =0; i<vertex_num; i++)
        {   int incident_counter=0;
            for(int x =0; x<edge_number; x++)
            {
               if(Value_not_Contained(edges[x][0],edges[x][1], &vertex_cover_VC_1))
               {
                    if(edges[x][0] == i){incident_counter++;}
                    if(edges[x][1] == i){incident_counter++;}
               }
            }

              Incidents_found.push_back(incident_counter);
        }
        int max_val=0;
        int index=0;
        int i=0;
        for (std::list<int>::iterator it = Incidents_found.begin(); it != Incidents_found.end(); ++it)
       {
           if(*it >max_val)
           {

               max_val=*it ;
               index=i;
           }
               i++;
       }
        if(max_val>0)
        {

        vertex_cover_VC_1.push_back(index);
        }
        else
        {
        exit_flag=1;
        }
    }  
    
    save_thread_timer(TL_APPROX_VC_1,&TS_APPROX_VC_1);
    lock_APPROX_VC_1->release();
    return 0;
}

void* APPROX_VC_2(void* unused)
{
     pthread_getcpuclockid(pthread_self(), &TL_APPROX_VC_2);
    while (lock_Parser->isHeld() == true) { /* wait */ }
     
    vector<vector<int> > edgList;
    // transfer 2d Edge content to vector and then vector of vectors
    int count = 0;
    for (int x = 0; x < edge_number; x++)
    {
      vector<int>newVec;
      for(int y = 0; y < 2; y++)
      {
        newVec.push_back(edges[x][y]);
        count ++;

        if(count == 2)
        {
          edgList.push_back(newVec);
          newVec.clear();
          count = 0;
        }
      }
    }

    // APPROX-VC-2
    vector<vector<int> > tempEdgList;

    tempEdgList = edgList;

    int helperCount = 0;

    int deleteTotal = 0;

    while(deleteTotal < edgList.size())
    {
      // store first edge i and j
      vertex_cover_VC_2.push_back(tempEdgList[0][0]);
      vertex_cover_VC_2.push_back(tempEdgList[0][1]);

      int node1 = tempEdgList[0][0];
      int node2 = tempEdgList[0][1];

      // loop through edges
      for (int i = 0; i<tempEdgList.size(); i++)
      {
        if ((tempEdgList[i][0] == node1) || (tempEdgList[i][0] == node2) || (tempEdgList[i][1] == node1) || (tempEdgList[i][1] == node2))
        {
            tempEdgList.erase(tempEdgList.begin() + i);
            deleteTotal+=1;

            i-=1;
        }
        else
        {
          //do nothing
        }

      }

      helperCount++;
    }//endWhile

    save_thread_timer(TL_APPROX_VC_2,&TS_APPROX_VC_2);
    lock_APPROX_VC_2->release();
    return 0;
    
}

int main()
{
    while(true)
    {
        lock_Parser->tryAcquire(); // lock Parser so everyone will wait for input
        // Thread Creation
        pthread_create(&thread_Parser, NULL, &Parser, NULL);
        while (lock_Parser->isHeld() == true) 
        {  
            if(eof_flag==1){ exit(0);}
        }
        pthread_create(&thread_CNF_SAT_VC, NULL, &CNF_SAT_VC, NULL);
        pthread_create(&thread_APPROX_VC_1, NULL, &APPROX_VC_1, NULL);
        pthread_create(&thread_APPROX_VC_2, NULL, &APPROX_VC_2, NULL);
        while (!All_Threads_finished()){/*wait*/}
        
          
        delete [] *edges;
        delete [] edges;
        status_flag=WAITING_FOR_VERTEX;
    }
    return 0;
}


// Functions definitions

bool Value_not_Contained(int val,int val2, vector<int> *v)
{   
    vector<int> vertex_cover=*v;
    for (int n = 0; n < vertex_cover.size(); ++n) 
    { 
        if(vertex_cover[n]==val2){ return false;}
        if(vertex_cover[n]==val){ return false;}
    }
    
    return true;
}

void Vertex_Cover_Printer(char *msg, vector<int> *v)
{   
    cout<<msg<<" ";
    vector<int> vertex_cover=*v;
    std::sort(vertex_cover.begin(), vertex_cover.end());
    for (int n = 0; n < vertex_cover.size(); ++n) 
    { 
        if(n == (vertex_cover.size()-1)){ cout<< vertex_cover[n]<< endl;}
        else{cout<< vertex_cover[n]<<",";}
    }
    
   vertex_cover.clear();
}

static void save_thread_timer( clockid_t cid , timespec *ts)
{
    if (clock_gettime(cid, &*ts) == -1)
        handle_error("clock_gettime");
}

bool All_Threads_finished()
{
    if((!(lock_CNF_SAT_VC->isHeld())) &&
       (!(lock_APPROX_VC_1->isHeld())) &&
       (!(lock_APPROX_VC_2->isHeld())))
    {
        return true;
    }
    return false;

}

////////////////////PARSER FUNCTIONS BEGIN
string trim(const string& str)
{
    size_t first = str.find_first_not_of(' ');
    if (string::npos == first)
    {
        return str;
    }
    size_t last = str.find_last_not_of(' ');
    return str.substr(first, (last - first + 1));
}

void command_parser(string input)
   {
      std::size_t vertex_ = input.find("V");
      std::size_t edge_ = input.find("E");
      std::size_t space = input.find(" ");
      
      // VERTEX COMMAND
      if ((vertex_ != -1) && ((space != -1))) { vertex_command(input, space); }
      //EDGE COMMAND
      else if ((edge_  != -1) && ((space != -1))) { edge_command(input, space); }
      //INVALID COMMAND
      else {std::cerr << " Error: Command not recognized \n";}
   }

void vertex_command(string input, size_t space)
   {
      
      input = input.substr(space, input.length() - 1); // Parse command from line
     vertex_num = atoi(input.c_str());// Convert parsed data
      if (vertex_num > 1)
      { 

         status_flag = WAITING_FOR_EDGES;
      }
      else
      {
         status_flag = WAITING_FOR_VERTEX;
      }

   }
   
void init_edge_vector(int vertex_num, int old_vertex_num)
   {

            
        edges = new int *[vertex_num] ;
        edges_VC_1 = new int *[vertex_num] ;
        for( int i = 0 ; i < vertex_num ; i++ )
        {
            edges[i] = new int[2];
            edges_VC_1[i] = new int[2];
        }
      
   }      
      
void edge_command(string input, size_t space)
{   
    if (status_flag == WAITING_FOR_EDGES) {
       int old_edge_number=edge_number;
       edge_number=edge_number_calc( input,  space);
       init_edge_vector(edge_number,old_edge_number);// Assign vertex num
       std::string s = input.substr(space, input.length() - 1); // Remove parsed command from line
       std::string delimiter = "}"; // delimiter of end of line
       size_t pos;
       std::string token;
       std::string token2;
       int i;
       while ((pos = s.find(delimiter)) != std::string::npos) // iterate through line to find data
       {
          size_t x = s.find(',') - 1 - s.find('<');
          size_t y = s.find('>') - 1 - s.find(',');
          token = s.substr(s.find('<') + 1, x);
          token2 = s.substr(s.find(',') + 1, y);
          int var1 = atoi(token.c_str());
          int var2 = atoi(token2.c_str());
          edges[i][0]=var1;
          edges[i][1]=var2;
          edges_VC_1[i][0]=var1;
          edges_VC_1[i][1]=var2;
          s.erase(0, s.find_first_of(">") + 2);// erase parsed data for next iteration/
          
          i++;
       }
       status_flag = GO_CALCULATE;
    }
    else if (status_flag == WAITING_FOR_VERTEX) 
    {
       std::cerr << " Error: need to assign number of vertex first use command V \n";
    }
    else if (status_flag == GO_CALCULATE) 
    {
       std::cerr << " Error: Edge list already captured to enter new list first change the # of vertexes according to the new list \n";
    }
    else if (status_flag == DONE_CALCULATING) 
    {
       std::cerr << " Error: Calculation for the provided input has been made enter a new vertex number and graph \n";
    }
}
          
int edge_number_calc(string input, size_t space)
{
   int i=0;
   std::string s = input.substr(space, input.length() - 1); // Remove parsed command from line
   string delimiter = "}"; // delimiter of end of line
   size_t pos;
   while ((pos = s.find(delimiter)) != std::string::npos) // iterate through line to find # edges
   {
      s.erase(0, s.find_first_of(">") + 2);// erase edge/
      i++;
   }
   return i;
}
