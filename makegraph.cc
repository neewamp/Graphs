#include<iostream>
#include<stdlib.h>
using namespace std;


//Run me with ./a.out <gnum> <number of vertices> <# of edges>
void makeGraph(int gnum, int numVert, int numEdges);



//Run me with ./a.out <gnum> <number of vertices> <# of edges>
int main(int argc, char* argv[])
{
  
  makeGraph(atoi(argv[1]),atoi(argv[2]),atoi(argv[3]));

}






void makeGraph(int gnum, int numVert, int numEdges){
  
 
  numVert++;
  cout << "Definition graph" << gnum << " := ";

  int e = 0;
  if (e < numEdges){
    for(int i = 1; i < numVert-1; i++){
      if (e > numEdges)
	break;
      for(int j = 2; j < numVert-1; j++){
	e++;
	if (e > numEdges)
	  break;
	cout << " (addEdge (" << i << "," << j << ")";
	
      }
    }

    for(int i = numVert-1; i >= 1; i--){
      if (e > numEdges)
	break;
      for(int j = numVert-1; j >= 2; j--){
	e++;
	if (e > numEdges)
	  break;
	cout << " (addEdge (" << i << "," << j << ")";
      }
    }
  }

  for(int i = 1; i < numVert;i++){
    cout << " (addVertex " << i << "";
  }
  cout << " empty";
  for(int i = 1; i < numVert;i++){
    cout << ")";
  }

  for(int i = 0; i < numEdges;i++){
    cout << ")";
  }

   
  cout << "."<<endl;

}
