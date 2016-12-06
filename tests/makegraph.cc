#include<stdio.h>
#include<iostream>
#include<stdlib.h>
#include<fstream>
using namespace std;

//Run me with ./a.out <gnum> <number of vertices> <# of edges>
void makeGraph(int gnum, int numVert, int numEdges, ofstream& fout);
void runSetG(int gnum);
void runIndG(int gnum);
//Run me with ./a.out <gnum> <number of vertices> <# of edges>
int main(int argc, char* argv[])
{
  ofstream fout;
  fout.open("graphtest.v");
  fout << "Require Import graph_inst.\n Open Scope positive_scope." << endl;
  for(int i = 1; i <= atoi(argv[1]); i++){
    makeGraph(i,atoi(argv[2]),atoi(argv[3]),fout);
    fout << "Definition test" << i <<" := myGraph.Vertices.elements (myGraph.neighborhood 1 graph" << i << ")." << endl;
    fout << "Definition test" << i << "'" << " := myGraph.Vertices.elements (g_prop.neighborhood 1 graph" << i << ")." << endl;
  }
  
  fout << "Extraction \"test.ml\" ";
  for(int i = 1; i <= atoi(argv[1]); i++){
    fout << "test" << i << " ";
    fout << "test" << i << "' ";
  }
  fout << "." << endl;
  system("coqc graphtest.v");
  for(int i = 1; i <= atoi(argv[1]); i++){
    runSetG(i);
    runIndG(i);
  }

}

void runSetG(int gnum)
{
  ofstream out;
  out.open("test.ml", std::ios_base::app);
  out << "let rec int_of_pos p = \n(match p with\n |XH -> 1\n|XO p' -> 2 * (int_of_pos p')\n|XI p' -> 2* (int_of_pos p') + 1)\n\n"
       << "let rec printer l =\n(match l with\n| [] -> Printf.printf " "\n|  (h:: t) -> Printf.printf \"%d \" h; printer t)\n\n"
       << "let print"<<gnum<<" =\nprinter (List.map int_of_pos (test"<< gnum << "));;\n\nlet () = Printf.printf \"\\n\";;\n"
       << "let time f=\nlet t = Sys.time() in\nlet fx = f in\nPrintf.printf \"Execution time: %fs\\n\" (Sys.time() -. t);\nfx\n\n"
      << "let t" << gnum << "' = time print"<<gnum<<" ;;" << endl;
  
}
void runIndG(int gnum)
{
  ofstream out;
  out.open("test.ml", std::ios_base::app);
  out << "let rec int_of_pos p = \n(match p with\n |XH -> 1\n|XO p' -> 2 * (int_of_pos p')\n|XI p' -> 2* (int_of_pos p') + 1)\n\n"
       << "let rec printer l =\n(match l with\n| [] -> Printf.printf " "\n|  (h:: t) -> Printf.printf \"%d \" h; printer t)\n\n"
       << "let print"<<gnum<<"' =\nprinter (List.map int_of_pos (test"<< gnum << "'));;\n\nlet () = Printf.printf \"\\n\";;\n"
       << "let time f=\nlet t = Sys.time() in\nlet fx = f in\nPrintf.printf \"Execution time: %fs\\n\" (Sys.time() -. t);\nfx\n\n"
      << "let t" << gnum << "' = time print"<<gnum<<"' ;;" << endl;
  
}











void makeGraph(int gnum, int numVert, int numEdges, ofstream& fout ){
 
  numVert++;
  fout << "Definition graph" << gnum << " := ";

  int e = 0;
  if (e < numEdges){
    for(int i = 1; i < numVert-1; i++){
      if (e > numEdges)
	break;
      for(int j = 2; j < numVert-1; j++){
	e++;
	if (e > numEdges)
	  break;
	fout << " (myGraph.addEdge (" << i << "," << j << ")";
	
      }
    }

    for(int i = numVert-1; i >= 1; i--){
      if (e > numEdges)
	break;
      for(int j = numVert-1; j >= 2; j--){
	e++;
	if (e > numEdges)
	  break;
	fout << " (myGraph.addEdge (" << i << "," << j << ")";
      }
    }
  }

  for(int i = 1; i < numVert;i++){
    fout << " (myGraph.addVertex " << i << "";
  }
  fout << " myGraph.empty";
  for(int i = 1; i < numVert;i++){
    fout << ")";
  }

  for(int i = 0; i < numEdges;i++){
    fout << ")";
  }

   
  fout << "."<<endl;

}
