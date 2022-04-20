//Roushan Prakash (190721)
//IME639 Project
#include<iostream>
#include<fstream>
#include<cmath>
#include"ilcplex/ilocplex.h"
#include"Header.h"

using namespace std;

ifstream fin("input.txt");
ofstream fout("output.txt");
//ofstream logt("logs.txt");

typedef IloArray<IloNumVarArray> Array2D;
typedef IloArray<Array2D> Array3D;
typedef IloArray<Array3D> Array4D;

vector< vector<int> > getAllSubsets(vector<int>& set)
{
	vector< vector<int> > subset;
	vector<int> empty;
	subset.push_back(empty);

	for (int i = 0; i < set.size(); i++)
	{
		vector< vector<int> > subsetTemp = subset;

		for (int j = 0; j < subsetTemp.size(); j++)
			subsetTemp[j].push_back(set[i]);

		for (int j = 0; j < subsetTemp.size(); j++)
			subset.push_back(subsetTemp[j]);
	}
	return subset;
}


int main(){

	
	int n = 0,T=0;
	
	int Q = 0, D = 0;
	vector<vector<vector<int>>>S;
	//vector<set<int>>comb_k;

	//Taking inputs
	fin >> n >> T >> Q >> D;
	vector<vector<int>> cij(n+1, vector<int>(n+1, 0));
	vector<int>q(n, 0);
	vector<int> R(T, 0);
	vector<vector<int>> dist(n+1, vector<int>(2, 0));
	dist[0][0] = 0;dist[0][1]=0;
	int a = 0, b = 0, c = 0, d = 0;
	for (int i = 0; i < n; i++) {
		fin >> a >> b >> c >> d;
		dist[i+1][0] = b; dist[i+1][1] = c;
		q[i] = d;
	}
	for (int i = 0; i <= n; i++) {
		for (int j = 0; j <= n; j++) {
			cij[i][j] = sqrt(((dist[i][0] - dist[j][0]) * (dist[i][0] - dist[j][0])) + ((dist[i][1] - dist[j][1]) * (dist[i][1] - dist[j][1])));
		}
	}
	/*for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			cout << cij[i][j] << " ";
		}
	}*/

	for (int i = 0; i < T; i++) {
		R[i] = 5;
	}

	for (int i = 0; i < n; i++) {
		if (q[i] <= 10) {
			vector<vector<int>>vnew;
			vector<int> v11{ 1,0,0,0,0 };
			vector<int> v12{ 0,1,0,0,0 };
			vector<int> v13{ 0,0,1,0,0 };
			vector<int> v14{ 0,0,0,1,0 };
			vector<int> v15{ 0,0,0,0,1 };
			vnew.push_back(v11); vnew.push_back(v12); vnew.push_back(v13); vnew.push_back(v14); vnew.push_back(v15);
			S.push_back(vnew);
		}
		else if ((q[i] > 10) && (q[i] <= 25)) {
			vector<vector<int>>vnew;
			vector<int> v1{ 1,0,1,0,0 };
			vector<int> v2{ 0,1,0,1,0 };
			vector<int> v3{ 0,0,1,0,1 };
			vnew.push_back(v1); vnew.push_back(v2); vnew.push_back(v3);
			S.push_back(vnew);
		}
		else {
			vector<vector<int>>vnew;
			vector<int> v1{ 1,1,1,1,1 };
			vnew.push_back(v1);
			S.push_back(vnew);
		}

	}
	/*for (int i = 0; i < S.size(); i++) {
		for (int j = 0; j < S[i].size(); j++) {
			for (int k = 0; k < S[i][j].size(); k++) {
				cout << S[i][j][k] << " ";
			}
		}cout << endl;
	}*/
	


	IloEnv env;
	IloArray<IloNumVarArray> xik(env,n);
	for(int i=0;i<n;i++)xik[i]= IloNumVarArray(env, S[i].size(), 0, 1, ILOINT);
	IloArray<IloNumVarArray>vit(env, n);
	for (int i = 0; i < n; i++)vit[i] = IloNumVarArray(env, T, 0, 1, ILOINT);
	/*IloArray<IloNumVarArray> akt(env, comb_k.size());
	for (int i = 0; i < comb_k.size(); i++)akt[i] = IloNumVarArray(env, T, 0, 1, ILOINT);*/
	Array3D aikt(env, n);
	for (int i = 0; i < n; i++) {
		aikt[i] = Array2D(env, S[i].size());
		for (int k = 0; k < S[i].size(); k++) {
			aikt[i][k] = IloNumVarArray(env, T);
			for (int t = 0; t < T; t++) {
				aikt[i][k][t] = IloNumVar(env, 0, 1, ILOINT);
			}
		}
	}

	Array4D uijtr(env, n);
	for (int i = 0; i < n; i++) {
		uijtr[i] = Array3D(env, n);
		for (int j = 0; j < n; j++) {
			uijtr[i][j] = Array2D(env, T);
			for (int t = 0; t < T; t++) {
				uijtr[i][j][t] = IloNumVarArray(env, R[t]);
				for (int r = 0; r < R[t]; r++) {
					uijtr[i][j][t][r] = IloNumVar(env, 0, 1, ILOINT);
				}
			}
		}
	}

	IloRangeArray constraint(env);
	for (int i = 1; i < n; i++) {
		IloExpr exp(env);
		for (int k = 0; k < S[i].size(); k++) {
			exp += xik[i][k];
		}
		constraint.add(exp == 1);
	}
	for (int i = 1; i < n; i++) {
		for (int t = 0; t < T; t++) {
			IloExpr exp(env);
			for (int k = 0; k < S[i].size(); k++) {
				exp += (xik[i][k] * aikt[i][k][t]);
			}
			//constraint.add(exp - vit[i][t] == 0);
		}
	}
	
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (i != j) {
				for (int t = 0; t < T; t++) {
					IloExpr exp(env);
					for (int r = 0; r < R[t]; r++) {
						exp += uijtr[i][j][t][r];
					}
					exp -= ((vit[i][t] + vit[j][t]) / 2);
					constraint.add(exp <= 0);
				}
			}
			
		}
	}

	for (int p = 0; p < n; p++) {
		for (int t = 0; t < T; t++) {
			for (int r = 0; r < R[t]; r++) {
				IloExpr exp(env);
				for (int i = 0; i < n; i++) {
					exp += uijtr[i][p][t][r];
				}
				for (int j = 0; j < n; j++) {
					exp -= uijtr[p][j][t][r];
				}
				constraint.add(exp == 0);
			}
		}
	}
	

	for (int j = 1; j < n; j++) {
		for (int t = 0; t < T; t++) {
			IloExpr exp(env);
			for (int r = 0; r < R[t]; r++) {
				for (int i = 0; i < n; i++) {
					exp += uijtr[i][j][t][r];
				}
			}
			constraint.add((exp - vit[j][t]) == 0);
		}
	}
	for (int t = 0; t < T; t++) {
		IloExpr exp(env);
		for (int r = 0; r < R[t]; r++) {
			for (int i = 0; i < n; i++) {
				exp += uijtr[i][0][t][r];
			}
		}
		constraint.add((exp - vit[0][t]) == 0);
	}

	for (int t = 0; t < T; t++) {
		for (int r = 0; r < R[t]; r++) {
			IloExpr exp(env);
			for (int j = 0; j < n; j++) {
				exp += uijtr[0][j][t][r];
			}
			constraint.add(exp <= 1);
		}
	}
	for (int t = 0; t < T; t++) {
		for (int r = 0; r < R[t]; r++) {
			IloExpr exp(env);
			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n; j++) {
					exp += uijtr[i][j][t][r];
				}
				exp *= q[i];
			}
			constraint.add(exp <= Q);
		}
	}
	
	for (int t = 0; t < T; t++) {
		for (int r = 0; r < R[t]; r++) {
			IloExpr exp(env);
			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n; j++) {
					exp += (cij[i][j] * uijtr[i][j][t][r]);
				}
			}
			constraint.add(exp <= D);
		}
	}
	
	//11th constraint
	vector<int> series;
	for (int i = 1; i <= n; i++)series.push_back(i);
	vector<vector<int>> subset;
	subset = getAllSubsets(series);
	
	subset.erase(subset.begin());
	
	for (int t = 0; t < T; t++) {
		for (int r = 0; r < R[t]; r++) {
			for (int p = 0; p < subset.size(); p++) {
				IloExpr exp(env);
				for (int i = 0; i < subset[p].size(); i++) {
					for (int j = 0; j < subset[p].size(); j++) {
						int re1 = subset[p][i]-1; int re2 = subset[p][j]-1;
						exp += uijtr[re1][re2][t][r];
					}
				}
				exp -= (subset[p].size() - 1);
				constraint.add(exp <= 0);
			}
		}
	}
	

	IloExpr objective(env);
	for (int t = 1; t < T; t++) {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				for (int r = 0; r < R[t]; r++) {
					objective += (cij[i][j] * uijtr[i][j][t][r]);
				}
			}
		}
	}
	
	IloModel Model(env);
	Model.add(IloMinimize(env, objective));
	objective.end();
	Model.add(constraint);
	cout << "a";
	IloCplex mp(Model);
	cout << "Roushan";
	mp.setOut(env.getNullStream());
	
	mp.solve();
	cout << "Optimal value is "<<mp.getObjValue();


	return 0;

}