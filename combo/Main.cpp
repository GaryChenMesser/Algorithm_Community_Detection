/*                                                                            
    Copyright 2014
    Alexander Belyi <alexander.belyi@gmail.com>,
    Stanislav Sobolevsky <stanly@mit.edu>                                               
                                                                            
    This is the main file of Combo algorithm.

    Combo is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Combo is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Combo.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <ctime>

#include "Graph.h"

#include <cmath>
#include <iostream>
#include <algorithm>
using namespace std;

//settings
const bool debug_verify = false;


#define INF 1000000000
//#define THRESHOLD 1e-6
#define THRESHOLD 0.1
const int RAND_MAX2 = RAND_MAX >> 1;

const double autoC1 = 2;
const double autoC2 = 1.5;
bool use_fixed_tries = false;
//gary
bool Inden = false;
Graph G;

double best_gain = 1.0;

vector<double> Sum(const vector< vector<double> >& matrix)
{
	int n = matrix.size();
	vector<double> res(n, 0.0);
	for(int i = 0; i < n; ++i)
		for(int j = 0; j < n; ++j)
			res[i] += matrix[i][j];
	return res;
}

template<typename T> bool Positive(T x) {return x > 0.0;}
template<typename T> bool Negative(T x) {return x < 0.0;}
template<typename T> bool NotNegative(T x) {return x >= 0.0;}
template<typename T> bool NotPositive(T x) {return x <= 0.0;}
vector<double> SumPos(const vector< vector<double> >& matrix, bool (*Pred)(double) = NULL)
{
	int n = matrix.size();
	vector<double> res(n, 0.0);
	for(int i = 0; i < n; ++i)
		for(int j = 0; j < n; ++j)
			if(Pred && Pred(matrix[i][j]))
				res[i] += matrix[i][j];
	return res;
}

template<typename T>
bool TestAll(const vector<T>& vec, bool (*Pred)(T))
{
	int n = vec.size();
	for(int i = 0; i < n; ++i)
		if(!Pred(vec[i]))
			return false;
	return true;
}

double ModGain(Graph& G, const vector< vector<double> >& Q, const vector<double>& correctionVector, const vector<int>& community, vector<int>& communityInd)
{
	if(Inden){
		int n = community.size();

		vector<int> NewOrig;
		vector<int> NewDest;
		for(size_t i = 0; i < communityInd.size(); ++i){
			if(community[i])NewOrig.push_back(communityInd[i]);
			else NewDest.push_back(communityInd[i]);
		}
		double IndenOldOrig = G.CalcInDen(communityInd);

		double IndenNewOrig = G.CalcInDen(NewOrig);
		double IndenNewDest = G.CalcInDen(NewDest);
		
		return IndenNewOrig * NewOrig.size() + IndenNewDest * NewDest.size();
	}
	
	else{
		int n = community.size();
		double mod_gain = 0.0;
		for(int i = 0; i < n; ++i)
		{
			for(int j = 0; j < n; ++j)
				if(community[i] == community[j])
					mod_gain += Q[i][j];
				else
					mod_gain -= Q[i][j];
		}
		mod_gain *= 0.5;
		for(int i = 0; i < n; ++i)
		{
			if(community[i])
				mod_gain += correctionVector[i];
			else
				mod_gain -= correctionVector[i];
		}
		return mod_gain;
	}
}

double PerformKernighansShift(const vector< vector<double> >& Q, const vector<double>& correctionVector, const vector<int>& communitiesOld, vector<int>& communitiesNew, const vector<int>& community) //perform a split improvement using a Karnigan-Lin-style iterative shifts series
{
	if(Inden){
		double g_max = 0;
		double g_max1 = 1;
		vector<int> oldOrig;
		vector<int> oldDest;

		for(size_t i = 0; i < community.size(); ++i){
			if(communitiesOld[i])oldOrig.push_back(community[i]);
			else oldDest.push_back(community[i]);
		}
		double inden_gain0 = G.CalcInDen(oldOrig) * oldOrig.size() + G.CalcInDen(oldDest) * oldDest.size();
		//cout << "oldOrig.size() = " << oldOrig.size() << endl;
		//cout << "oldDest.size() = " << oldDest.size() << endl;
		//cout << "G.CalcInDen(oldOrig) = " << G.CalcInDen(oldOrig) << endl;
		//cout << "G.CalcInDen(oldDest) = " << G.CalcInDen(oldDest) << endl;
		//cout << "inden_gain0 = " << inden_gain0 << endl;
		while(g_max1 - g_max > 0){
			g_max1 = g_max;
			g_max = 0;
			vector<double> gv;
			vector<int> mv;
			//vector<int> bv;			
			vector<int> tempOrig = oldOrig;
			vector<int> tempDest = oldDest;
			double minima1 = 100;
			double minima2 = 100;
			while(tempOrig.size() > 2 && tempDest.size() > 2){
				vector<double> all_da;
				vector<double> all_db;
				for(size_t i = 0; i < tempOrig.size(); ++i){
					double degree = 0;
					for(size_t j = 0; j < tempOrig.size(); ++j)
						degree -= G.EdgeWeight(tempOrig[i], tempOrig[j]);
					degree /= ((tempOrig.size() - 2) * (tempOrig.size() - 1));
					
					for(size_t j = 0; j < tempDest.size(); ++j)
						degree += G.EdgeWeight(tempOrig[i], tempDest[j]);
					degree /= (tempDest.size() * (tempDest.size() + 1));
					
					all_da.push_back(degree);
				}
				for(size_t i = 0; i < tempDest.size(); ++i){
					double degree = 0;
					for(size_t j = 0; j < tempDest.size(); ++j)
						degree -= G.EdgeWeight(tempDest[i], tempDest[j]);
					degree /= ((tempDest.size() - 2) * (tempDest.size() - 1));
					
					for(size_t j = 0; j < oldOrig.size(); ++j)
						degree += G.EdgeWeight(tempDest[i], tempOrig[j]);
					degree /= (tempOrig.size() * (tempOrig.size() + 1));
					
					all_db.push_back(degree);
				}
				vector<double>::iterator result1;
				vector<double>::iterator result2;

				result1 = max_element(all_da.begin(), all_da.end());
				//cout << "result1 = " << *result1 << endl;
				//cout << "distance(all_da.begin(), result1)" << distance(all_da.begin(), result1) << endl;
				//cout << "tempOrig[distance(all_da.begin(), result1)]" << tempOrig[distance(all_da.begin(), result1)] << endl;
				//cout << "tempOrig.size() = " << tempOrig.size() << endl;
				result2 = max_element(all_db.begin(), all_db.end());
				//cout << "result2" << *result2 << endl;
				//cout << "distance(all_db.begin(), result2)" << distance(all_db.begin(), result2) << endl;
				//cout << "tempDest[distance(all_db.begin(), result2)]" << tempDest[distance(all_db.begin(), result2)] << endl;
				//cout << "tempDest.size() = " << tempDest.size() << endl;
				if(*result1 > *result2){
					if(*result1 <= 0)break;
					mv.push_back(tempOrig[distance(all_da.begin(), result1)]);
					//cout << "mv = " << mv.back() << endl;;
					//cout << communitiesOld[distance(community.begin(), find(community.begin(), community.end(), mv.back()))] << endl;
					if(communitiesOld[distance(community.begin(), find(community.begin(), community.end(), mv.back()))] == 0){
						mv.pop_back();
						break;
					}
					tempOrig.erase(find(tempOrig.begin(), tempOrig.end(), mv.back()));
					tempDest.push_back(mv.back());
					g_max += *result1;
				}
				else{
					if(*result2 <= 0)break;
					mv.push_back(tempDest[distance(all_db.begin(), result2)]);
					//cout << "mv = " << mv.back() << endl;
					//cout << communitiesOld[distance(community.begin(), find(community.begin(), community.end(), mv.back()))] << endl;				
					if(communitiesOld[distance(community.begin(), find(community.begin(), community.end(), mv.back()))]){
						mv.pop_back();
						break;
					}
					tempDest.erase(find(tempDest.begin(), tempDest.end(), mv.back()));
					tempOrig.push_back(mv.back());
					g_max += *result2;
				}
			}

			// exchange
			//cout << "mv.size() = " << mv.size() << endl;
			//cout << "g_max = " << g_max << endl;
			for(size_t i = 0; i < mv.size(); ++i){
				vector<int>::iterator it = find(oldOrig.begin(), oldOrig.end(), mv[i]);
				if(it != oldOrig.end()){
					oldOrig.erase(it);
				}
				else {
					oldOrig.push_back(mv[i]);
				}
				it = find(oldDest.begin(), oldDest.end(), mv[i]);
				if(it != oldDest.end()){
					oldDest.erase(it);
				}
				else {
					oldDest.push_back(mv[i]);
				}
			}
			double inden_gain1 = G.CalcInDen(oldOrig) * oldOrig.size() + G.CalcInDen(oldDest) * oldDest.size();
		}
		// store to communityNew
		cout << "\n-----oldOrig-----\n";
		for(size_t i = 0; i < oldOrig.size(); ++i){
			cout << oldOrig[i] << " ";
			if(find(community.begin(), community.end(), oldOrig[i]) == community.end())cerr << "error!\n\n";
			communitiesNew[distance(community.begin(), find(community.begin(), community.end(), oldOrig[i]))] = 1;
		}
		cout << "\n-----oldDest-----\n";
		for(size_t i = 0; i < oldDest.size(); ++i){
			cout << oldDest[i] << " ";
			if(find(community.begin(), community.end(), oldDest[i]) == community.end())cerr << "error!\n\n";
			communitiesNew[distance(community.begin(), find(community.begin(), community.end(), oldDest[i]))] = 0;
		}
		for(size_t i = 0; i < communitiesNew.size(); ++i)cout << communitiesNew[i] << " ";
		cout << endl;
		cout << "inden1 = " << G.CalcInDen(oldOrig) << endl;
		cout << "inden2 = " << G.CalcInDen(oldDest) << endl;
		double inden_gain1 = G.CalcInDen(oldOrig) * oldOrig.size() + G.CalcInDen(oldDest) * oldDest.size();
		cout << "result111 = " << inden_gain1 - inden_gain0 << endl;
		cout << "inden = " << inden_gain1 << endl;
		return inden_gain1;
	}
	else{
		int n = Q.size();
		vector<double> gains(n, 0.0);
		for(int i = 0; i < n; ++i)
		{
			for(int j = 0; j < n; ++j)
				if(i != j)
					if(communitiesOld[i] == communitiesOld[j])
						gains[i] -= Q[i][j];
					else
						gains[i] += Q[i][j];
			if(communitiesOld[i])
				gains[i] -= correctionVector[i];
			else
				gains[i] += correctionVector[i];
			gains[i] *= 2;
		}
		vector<double> gains_got(n, 0.0);
		vector<int> gains_indexes(n, 0);
		communitiesNew = communitiesOld;
		for(int i = 0; i < n; ++i)
		{
			vector<double>::iterator it = max_element(gains.begin(), gains.end());
			gains_got[i] = *it;
			int gains_ind = it - gains.begin();
			gains_indexes[i] = gains_ind;
			if(i > 0)
				gains_got[i] = gains_got[i] + gains_got[i-1];
			for(int j = 0; j < n; ++j)
				if(communitiesNew[gains_ind] == communitiesNew[j])
					gains[j] += 4 * Q[gains_ind][j];
				else
					gains[j] -= 4 * Q[gains_ind][j];
			communitiesNew[gains_ind] = !communitiesNew[gains_ind];
			gains[gains_ind] = gains[gains_ind] - 2*n;
		}
		vector<double>::iterator it = max_element(gains_got.begin(), gains_got.end());
		double mod_gain = *it;
		int stepsToGetMaxGain = it - gains_got.begin() + 1;
		if(mod_gain > 0)
		{
			communitiesNew = communitiesOld;
			for(int i = 0; i < stepsToGetMaxGain; ++i)
				communitiesNew[gains_indexes[i]] = !communitiesNew[gains_indexes[i]];
		}
		else
		{
			communitiesNew = communitiesOld;
			mod_gain = 0;
		}
		return mod_gain;
	}
 	
}

double Split(Graph& G, vector< vector<double> >& Q, const vector<double>& correctionVector, vector<int>& splitCommunity, vector<int>& communityInd) //try to split the subnetwork with respect to the correction vector
{
	double mod_gain = 0.0;
	vector<double> sumQ = Sum(Q);
	//if(Q.size() != splitCommunity.size())cout << "wrong! Q.size() != splitCommunity.size()\n";
	int n = splitCommunity.size();
	if(Q.size() != 0){
		for(int i = 0; i < n; ++i)
			Q[i][i] += 2 * correctionVector[i] - sumQ[i]; //adjust the submatrix
	}
	int tries;
	if(use_fixed_tries)
		tries = 2;
	else
		tries = pow(abs(log(best_gain)), autoC2) / autoC1 + 3;
	int tryI = 0;
	while(tryI < tries)
	{
		tryI = tryI + 1;

		//perform an initial simple split
		vector<int> communities0(n);
		if(use_fixed_tries)
			communities0.assign(n, 2 - tryI);
		else
			for(int i = 0; i < n; ++i)
				communities0[i] = rand() < RAND_MAX2;
		double mod_gain0 = ModGain(G, Q, correctionVector, communities0, communityInd);
		double mod_gain1 = 1000;
		if(Inden){
			while(mod_gain1 - mod_gain0 > THRESHOLD)
			{
				vector<int> communitiesNew(n);
				mod_gain1 = PerformKernighansShift(Q, correctionVector, communities0, communitiesNew, communityInd);
				if(mod_gain1 - mod_gain0 > THRESHOLD)
				{
					mod_gain0 = mod_gain1;
					communities0 = communitiesNew;
					if(debug_verify)
					{
						double mod_gain_verify = ModGain(G, Q, correctionVector, communities0, communityInd);
						if(fabs(mod_gain_verify - mod_gain0) > THRESHOLD)
							cerr << "ERROR\n";
					}
				}
			}
		}
		else{
			while(mod_gain1 > THRESHOLD)
			{
				vector<int> communitiesNew(n);
				mod_gain1 = PerformKernighansShift(Q, correctionVector, communities0, communitiesNew, communityInd);
				if(mod_gain1 > THRESHOLD)
				{
					mod_gain0 = mod_gain0 + mod_gain1;
					communities0 = communitiesNew;
					if(debug_verify)
					{
						double mod_gain_verify = ModGain(G, Q, correctionVector, communities0, communityInd);
						if(fabs(mod_gain_verify - mod_gain0) > THRESHOLD)
							cerr << "ERROR\n";
					}
				}
			}
		}
		if(mod_gain < mod_gain0)
		{
			splitCommunity = communities0;
			mod_gain = mod_gain0;
		}
		if(mod_gain <= 1e-6)
			tries = int(tries / 2);
	}

	if(fabs(mod_gain) < THRESHOLD)
		splitCommunity.assign(n, 1);
	cout << "finished!\n";
	return mod_gain;
}

void reCalc(Graph& G, vector< vector<double> >& moves, vector< vector<int> >& splits_communities, int origin, int dest)
{
	moves[origin][dest] = 0;
	if(origin != dest)
	{
		vector<int> origCommInd = G.CommunityIndices(origin);
		if(!origCommInd.empty())
		{
			if(Inden){
				vector<double> correctionVector;
				vector<int> splitComunity(origCommInd.size(), 0);
				vector< vector<double> > Q;
				moves[origin][dest] = Split(G, Q, correctionVector, splitComunity, origCommInd);
				cout << "splitted\n";
				for(int i = 0; i < splitComunity.size(); ++i)
					splits_communities[dest][origCommInd[i]] = splitComunity[i];
			} else{
				vector<double> correctionVector = G.GetCorrectionVector(origCommInd, G.CommunityIndices(dest));
				vector<int> splitComunity(origCommInd.size());
				vector< vector<double> > Q = G.GetModularitySubmatrix(origCommInd);
				moves[origin][dest] = Split(G, Q, correctionVector, splitComunity, origCommInd);
				for(int i = 0; i < splitComunity.size(); ++i)
					splits_communities[dest][origCommInd[i]] = splitComunity[i];
			}
		}
	}
}

double BestGain(const vector< vector<double> >& moves, int& origin, int& dest)
{
	double bestGain = -1;
	for(int i = 0; i < moves.size(); ++i)
		for(int j = 0; j < moves.size(); ++ j)
			if(bestGain < moves[i][j])
			{
				bestGain = moves[i][j];
				origin = i;
				dest = j;
			}
	return bestGain;
}

void DeleteEmptyCommunities(Graph& G, vector< vector<double> >& moves, vector< vector<int> >& splits_communities, int origin)
{
	if(G.DeleteCommunityIfEmpty(origin))
	{
		int commNumber = G.CommunityNumber();
		for(int i = origin; i < commNumber; ++i)
			moves[i] = moves[i+1];
		moves[commNumber].assign(commNumber+2, 0);
		for(int i = 0; i < moves.size(); ++i)
		{
			for(int j = origin; j < commNumber+1; ++j)
				moves[i][j] = moves[i][j+1];
			moves[i][commNumber+1] = 0;
		}
		for(int i = origin; i < commNumber+1; ++i)
			splits_communities[i] = splits_communities[i+1];
	}
}

void RunCombo(Graph& G, int max_comunities)
{	
	//gary
	if(Inden){
		//G.CalcConMtrix();
	} else{
		G.CalcModMtrix();
	}
	G.SetCommunities(vector<int>(G.Size(), 0));
	double currentCon;
	double currentMod;
	if(Inden){
		//currentCon = G.myConductance();
	} else{
		currentMod = G.Modularity();
	}
	//cerr << "Initial modularity: " << currentMod << endl;
	vector< vector<double> > moves(2, vector<double>(2, 0)); //results of splitting communities 
	//vectors of boolean meaning that corresponding vertex should be moved to dest
	vector< vector<int> > splits_communities(2, vector<int>(G.Size(), 0)); //best split vectors

	int origin, dest;
	for(origin = 0; origin < G.CommunityNumber(); ++ origin)
		for(dest = 0; dest < G.CommunityNumber() + (G.CommunityNumber() < max_comunities); ++dest)
			reCalc(G, moves, splits_communities, origin, dest);
	cout << "Modularity = " << G.Modularity() << endl;
	best_gain = BestGain(moves, origin, dest);
	double best_gain1 = 0;
	while(best_gain > THRESHOLD)
	{
		bool comunityAdded = dest >= G.CommunityNumber();
		G.PerformSplit(origin, dest, splits_communities[dest]);
		if(debug_verify)
		{
			double oldMod = currentMod;
			currentMod = G.Modularity();
			if(fabs(currentMod - oldMod - best_gain) > THRESHOLD)
				cerr << "ERROR\n";
		}
		if(comunityAdded && dest < max_comunities - 1)
		{
			if(dest >= moves.size() - 1)
			{
				for(int i = 0; i < moves.size(); ++i)
					moves[i].push_back(0);
				moves.push_back(vector<double>(moves.size() + 1, 0));
				splits_communities.push_back(vector<int>(G.Size(), 0));
			}
			for(int i = 0; i < dest; ++i)
			{
				moves[i][dest+1] = moves[i][dest];
				splits_communities[dest+1] = splits_communities[dest];
			}
		}

		for(int i = 0; i < G.CommunityNumber() + (G.CommunityNumber() < max_comunities); ++i)
		{cout << "i = " << i << endl;
			reCalc(G, moves, splits_communities, origin, i);
			cout << "Modularity = " << G.Modularity() << endl;
			reCalc(G, moves, splits_communities, dest, i);
			cout << "Modularity = " << G.Modularity() << endl;
			if(i != dest && i < G.CommunityNumber())
				reCalc(G, moves, splits_communities, i, origin);
			if(i != origin && i < G.CommunityNumber())
				reCalc(G, moves, splits_communities, i, dest);
			cout << "Modularity = " << G.Modularity() << endl;
		}
		//DeleteEmptyCommunities(G, moves, splits_communities, origin); //remove origin community if empty
		if(Inden)best_gain1 = best_gain;
		best_gain = BestGain(moves, origin, dest);
		if(Inden)best_gain -= best_gain1;
	}
}

int main(int argc, char** argv)
{
	int max_comunities = INF;
	if(argc < 2)
	{
		cout << "Error: provide path to edge list (.edgelist) or pajeck (.net) file" << endl;
		return -1;
	}
	if(argc > 2)
	{
		if(string(argv[2]) != "INF")
		max_comunities = atoi(argv[2]);
	}
	if(argc > 4)
		use_fixed_tries = atoi(argv[4]);
	if(argc > 3){
		Inden = 1;
		cout << "Scoring function: Internal density.\n";
	}
	else cout << "Scoring function: Modularity.\n";

	string fileName = argv[1];
	srand(time(0));

	
	string ext = fileName.substr(fileName.rfind('.'), fileName.length() - fileName.rfind('.'));
	if(ext == ".edgelist")
		G.ReadFromEdgelist(fileName);
	else if(ext == ".net")
		G.ReadFromPajeck(fileName);
	if(G.Size() <= 0)
	{
		cout << "Error: graph is empty" << endl;
		return -1;
	}
	
	clock_t startTime = clock();
	RunCombo(G, max_comunities);

	//cout << fileName << " " << G.Modularity() << endl;
	//cout << "Elapsed time is " << (double(clock() - startTime)/CLOCKS_PER_SEC) << endl;

	G.PrintCommunity(fileName.substr(0, fileName.rfind('.')) + "_comm_comboC++.txt");
	cout << G.Modularity() << endl;
	return 0;
}
