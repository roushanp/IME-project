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
			cij[i][j] = 1.3*sqrt(((dist[i][0] - dist[j][0]) * (dist[i][0] - dist[j][0])) + ((dist[i][1] - dist[j][1]) * (dist[i][1] - dist[j][1])));
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
	IloRangeArray constraint1(env);
	IloArray<IloNumVarArray> xik(env,n);
	for(int i=0;i<n;i++)xik[i]= IloNumVarArray(env, n, 0, 1, ILOINT);
	IloArray<IloNumVarArray>vit(env, n);
	for (int i = 0; i < n; i++)vit[i] = IloNumVarArray(env, T, 0, 1, ILOINT);
	Array3D aikt(env, n);
	for (int i = 0; i < n; i++) {
		aikt[i] = Array2D(env, n);
		for (int k = 0; k < n; k++) {
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
	IloExpr exp1(env);

	//Constraint 6
	for (int i = 1; i < n; i++) {
		IloExpr exp(env);
		for (int k = 0; k < S[i].size(); k++) {
			for (int p = 0; p < n; p++) {
				if(S[i][k][p])exp += xik[i][p];
			}
		}
		constraint1.add(exp == 1);
	}
	

	//Constraint7
	for (int i = 1; i < n; i++) {
		for (int t = 0; t < T; t++) {
			IloExpr exp(env);
			for (int k = 0; k < S[i].size(); k++) {
				for (int p = 0; p < n; p++) {
					if(S[i][k][p])exp += xik[i][p]*aikt[i][p][t];
				}
			}
			constraint1.add(exp >= n);
		}
	}
	
	//Constraint8
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

	//Constraint9
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
				constraint1.add(exp == 0);
			}
		}
	}
	
	//Constraint10
	for (int j = 1; j < n; j++) {
		for (int t = 0; t < T; t++) {
			IloExpr exp(env);
			for (int r = 0; r < R[t]; r++) {
				for (int i = 0; i < n; i++) {
					exp += uijtr[i][j][t][r];
				}
			}
			constraint1.add((exp - vit[j][t]) == 0);
		}
	}

	//Constraint10
	for (int t = 0; t < T; t++) {
		IloExpr exp(env);
		for (int r = 0; r < R[t]; r++) {
			for (int i = 0; i < n; i++) {
				exp += uijtr[i][0][t][r];
			}
		}
		constraint.add((exp - vit[0][t]) == 0);
	}
	//Constraint 11
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
						int re1 = subset[p][i] - 1; int re2 = subset[p][j] - 1;
						exp += uijtr[re1][re2][t][r];
					}
				}
				exp -= (subset[p].size() - 1);
				constraint.add(exp <= 0);
			}
		}
	}
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			for (int t = 0; t < T; t++) {
				for (int r = 0; r < R[t]; r++) {
					exp1 += uijtr[i][j][t][r];
				}
			}
		}
	}constraint.add(exp1 >= 2 * n);

	for (int i = 1; i < n; i++) {
		for (int t = 0; t < T; t++) {
			IloExpr exp(env);
			for (int k = 0; k < S[i].size(); k++) {
				for (int p = 0; p < n; p++) {
					exp += aikt[i][p][t];
				}

			}
			constraint.add(exp >= n);
		}
	}
	

	//Constraint 12
	for (int t = 0; t < T; t++) {
		for (int r = 0; r < R[t]; r++) {
			IloExpr exp(env);
			for (int j = 0; j < n; j++) {
				exp += uijtr[0][j][t][r];
			}
			constraint.add(exp <= 1);
		}
	}

	//Constraint13
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
	
	//Constraint14
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
	
	//Objective function
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
	IloCplex mp(Model);
	mp.setOut(env.getNullStream());
	
	mp.solve();
	fout << "Optimal value is "<<ceil(mp.getObjValue());

	return 0;

}