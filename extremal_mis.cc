//
// File: extremal_mis.cc
// Author: David W. Juedes
// Purpose: Finds the extremal graphs related to the number of maximal
// independent sets.
// In particular, this prints out the graphs with the most maximal independent
// sets of each size.
#include <set>
#include <iostream>
#include <list>
#include <vector>
#include <algorithm>
using namespace std;

vector<pair<int,int> > all_edges(int n) {
  vector<pair<int,int> > temp;
  for (int i=0;i<n;i++) {
    for (int j=i+1;j<n;j++) {
      temp.push_back(make_pair(i,j));
    }
  }
  return temp;
}

vector<set<int> > create_graph(int n, vector<pair<int,int> > &edges) {
  vector<set<int> > G1;
  G1.resize(n);
  for (int i=0;i<edges.size();i++) {
    G1[edges[i].first].insert(edges[i].second);
    G1[edges[i].second].insert(edges[i].first);
  }
  return G1;
} 

// Six Possible Edges for a graph of size 4.
// Hence, there are 2^6 = 64 possible graphs.
//
//
// Each graph has 2^4 = 16 possible subsets.
// Each of these could or could not be maximal independent sets.
//

  

bool IS(set<int> &I, vector<set<int> > &G) {
  for (set<int>::iterator p = I.begin();
       p!=I.end();++p) {
    for (set<int>::iterator p1=I.begin();p1!=I.end();++p1) {
      if ((*p)!=(*p1)) {
	if (G[*p].count(*p1) > 0) return false;
	if (G[*p1].count(*p) >0) return false;
      }
    }
  }
  return true;
}

bool MIS(set<int> &I, vector<set<int> > &G) {
  int n = G.size();
  if (!IS(I,G)) return false;
  for (int i=0;i<n;i++) {
    if (I.count(i) == 0) {
      set<int> T;
      T=I;
      T.insert(i);
      if (IS(T,G)) return false;
    }
  }
  return true;
}

//
// Generates all subsets of the set {0..n-1}
//
vector<set<int> > all_subsets(int n) {
  vector<set<int> > all_s;
  int n2 = 1<<n;

  for (int j=0;j<n2;j++) {
    set<int> t;
    for (int k=0;k<n;k++) {
      if ((j&(1<<k))>0) {
	t.insert(k);
      }
    }
    all_s.push_back(t);
  }
  return all_s;
}


//
// Generates all graphs of size n
//
vector<vector<set<int> > > all_graphs(int n) {
  vector<vector<set<int> > > all_g;
  vector<pair<int,int> > all_e;
  all_e = all_edges(n);
  int m = all_e.size();
  int m2 = 1<<m;
  
  for (int j=0;j<m2;j++) {
    vector<pair<int,int> > t1;
    for (int k=0;k<all_e.size();k++) {
      if ((j&(1<<k))>0) {
	t1.push_back(all_e[k]);
      }
    }
    all_g.push_back(create_graph(n,t1));
  }
  return all_g;
}

void printG(vector<set<int> > &G) {
  int n = G.size();
  for (int i=0;i<n;i++) {
    cout << i <<":";
    for (set<int>::iterator p = G[i].begin();
	 p!=G[i].end();++p) {
      cout << " " << *p;
    }
    cout << endl;
  }
}

// Counts the number of maximal independent sets in graphs of size n;

void count_MIS(int n) {
  vector<pair<int,int> > all_e;
  all_e = all_edges(n);
  cout << "Number of possibles edges for a graph of size "<<n<<"  = " << all_e.size() << endl;
  vector<set<int> > all_s;
  all_s = all_subsets(n);
  cout << "Number of possible subsets of with at most "<< n << " elements = " << all_s.size() << endl;
  //vector<vector<set<int> > > all_g;
  //all_g = all_graphs(n);
  //cout << "Number of possible graphs of with "<< n << " vertices = " << all_g.size() << endl;

  int maxMIS = 0;
  vector<set<int> > maxG;
  int m = all_e.size();
  int m2 = 1<<m;
  for (int i=0;i<m2;i++) {
    vector<pair<int,int> > GX;
    for (int k=0;k<m;k++) {
      if ((i&(1<<k))>0) {
	GX.push_back(all_e[k]);
      }
    }
    vector<set<int> > G = create_graph(n,GX);
    
    //for (int i=0;i<all_g.size();i++) {
    int sumMIS=0;
    for (int j=0;j<all_s.size();j++) {
      if (MIS(all_s[j],G)) {
	sumMIS++;
      }
    }
    if (sumMIS >maxMIS) {
      maxG=G;
      maxMIS = sumMIS;
    }
    //   cout << "MIS total for graph " << i << " = " << sumMIS << endl;
  }
  cout << "Maximum number of MISs" << maxMIS << endl;
  cout << "Extremal graph = " << endl;
  printG(maxG);
}
  
int main() {
  count_MIS(1);
  count_MIS(2);
  count_MIS(3);
  count_MIS(4);
  count_MIS(5);
  count_MIS(6);
  count_MIS(7);
  
  //vector<pair<int,int> > starting_point;

  //starting_point = all_edges(4);

  //cout << starting_point.size() << endl;
  //vector<vector<set<int> > > all_gs;

  //all_gs = all_graphs(4);
  //cout << all_gs.size() << endl;
  //vector<set<int> > all_s;
  //all_s = all_subsets(4);
  //cout << all_s.size() << endl;
}
  
