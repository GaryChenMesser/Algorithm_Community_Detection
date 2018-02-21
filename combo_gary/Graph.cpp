/*                                                                            
    Copyright 2014
    Alexander Belyi <alexander.belyi@gmail.com>,
    Stanislav Sobolevsky <stanly@mit.edu>                                               
                                                                            
    This file is part of Combo algorithm.

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

#include "Graph.h"

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <set>
#include <algorithm>
using std::ifstream;
using std::ofstream;
using std::string;
using std::vector;
using std::set;
using std::max;
using std::cout;
using std::endl;
using std::min;

Graph::Graph(void)
{
	m_size = 0;
	m_totalWeight = 0.0;
	m_isOriented = false;
	m_communityNumber = 0;
}


Graph::~Graph(void)
{
}

void Graph::FillMatrix(const vector<int>& src, const vector<int>& dst, const vector<double>& weight)
{
	int m = min(*min_element(src.begin(), src.end()), *min_element(dst.begin(), dst.end()));
	if(m > 0)
		m = 1;
	if(!m_isOriented)
		m_totalWeight *= 2;
	m_size = 1 + max(*max_element(src.begin(), src.end()), *max_element(dst.begin(), dst.end())) - m;
	m_matrix.assign(m_size, vector<double>(m_size, 0));
	for(int i = 0; i < src.size(); ++i)
	{
		m_matrix[src[i]-m][dst[i]-m] += weight[i];
		if(!m_isOriented)
			m_matrix[dst[i]-m][src[i]-m] += weight[i];
	}
}

void Graph::FillModMatrix(const vector<int>& src, const vector<int>& dst, const vector<double>& weight)
{
	int m = min(*min_element(src.begin(), src.end()), *min_element(dst.begin(), dst.end()));
	if(m > 0)
		m = 1;
	m_size = 1 + max(*max_element(src.begin(), src.end()), *max_element(dst.begin(), dst.end())) - m;
	if(!m_isOriented)
		m_totalWeight *= 2;
	m_modMatrix.assign(m_size, vector<double>(m_size, 0));
	vector<double> sumQ2(m_size, 0.0);
	vector<double> sumQ1(m_size, 0.0);
	for(int i = 0; i < src.size(); ++i)
	{
		m_modMatrix[src[i]-m][dst[i]-m] += weight[i] / m_totalWeight;
		if(!m_isOriented)
			m_modMatrix[dst[i]-m][src[i]-m] += weight[i] / m_totalWeight;
	
		sumQ1[src[i]-m] += weight[i] / m_totalWeight;
		sumQ2[dst[i]-m] += weight[i] / m_totalWeight;
		if(!m_isOriented)
		{
			sumQ1[dst[i]-m] += weight[i] / m_totalWeight;
			sumQ2[src[i]-m] += weight[i] / m_totalWeight;
		}
	}
	for(int i = 0; i < m_size; ++i)
		for(int j = 0; j < m_size; ++j)
			m_modMatrix[i][j] -= sumQ1[i]*sumQ2[j];
	for(int i = 0; i < m_size; ++i)
		for(int j = 0; j < m_size; ++j)
			m_modMatrix[i][j] = m_modMatrix[j][i] = (m_modMatrix[i][j] + m_modMatrix[j][i]) / 2;
}

void Graph::ReadFromEdgelist(const std::string& fname)
{
	ifstream file(fname.c_str());
	if(!file.is_open())
		return;
	vector<int> src, dst;
	vector<double> weight;
	while(file.good())
	{
		char buff[256];
		file.getline(buff, 255);
		int s = -1, d = -1;
		double w = 1.0;
		sscanf(buff, "%d %d %lf", &s, &d, &w);
		if(s != -1 && d != -1)
		{
			src.push_back(s);
			dst.push_back(d);
			weight.push_back(w);
			m_totalWeight += w;
		}
	}
	file.close();
	FillMatrix(src, dst, weight);
	FillModMatrix(src, dst, weight);
}

void Graph::ReadFromPajeck(const std::string& fname)
{
	ifstream file(fname.c_str());
	if(!file.is_open())
		return;
	vector<int> src, dst;
	vector<double> weight;
	bool skip = true;
	while(file.good())
	{
		char buff[256];
		file.getline(buff, 255);
		string line = buff;
		if(line == "*Edges")
		{
			skip = false;
			m_isOriented = false;
		}
		else if(line == "*Arcs")
		{
			skip = false;
			m_isOriented = true;
		}
		else if(!skip)
		{
			int s = -1, d = -1;
			double w = 1.0;
			sscanf(buff, "%d %d %lf", &s, &d, &w);
			if(s != -1 && d != -1)
			{
				src.push_back(s);
				dst.push_back(d);
				weight.push_back(w);
				m_totalWeight += w;
			}
		}
	}
	file.close();
	FillMatrix(src, dst, weight);
	FillModMatrix(src, dst, weight);
}

double Graph::EdgeWeight(int i, int j) const
{
	if(i >= m_matrix.size() || j >= m_matrix[0].size())cout << "error! in EdgeWeight(i, j)!";
	return m_matrix[i][j];
}

void Graph::CalcModMtrix()
{
	if(!m_modMatrix.empty())
		return;

	m_modMatrix.assign(m_size, vector<double>(m_size, 0.0));
	for(int i = 0; i < m_size; ++i)
		for(int j = 0; j < m_size; ++j)
			m_modMatrix[i][j] = EdgeWeight(i, j) / m_totalWeight;
	
	vector<double> sumQ2(m_size, 0.0);
	vector<double> sumQ1(m_size, 0.0);
	for(int i = 0; i < m_size; ++i)
		for(int j = 0; j < m_size; ++j)
		{
			sumQ1[i] += m_modMatrix[i][j];
			sumQ2[j] += m_modMatrix[i][j];
		}
	for(int i = 0; i < m_size; ++i)
		for(int j = 0; j < m_size; ++j)
			m_modMatrix[i][j] -= sumQ1[i]*sumQ2[j];
	for(int i = 0; i < m_size; ++i)
		for(int j = 0; j < m_size; ++j)
			m_modMatrix[i][j] = m_modMatrix[j][i] = (m_modMatrix[i][j] + m_modMatrix[j][i]) / 2;
}

//gary
int Graph::numCommunity(const vector<int>& community) const
{
	vector<int> num;
	for(int i = 0; i < community.size(); ++i){
		for(int j = 0; j < num.size() + num.size()==0; ++j){
			if(num.size()==0)num.push_back(community[i]);
			if(num[j] != community[i] && num.size() - 1 == j)num.push_back(community[i]);
			else{
				if(num[j] == community[i])break;
			}
		}
	}
	return num.size();
}

//gary
/*
vector<double> Graph::CalcConMtrix(const vector<int>& communityInd)
{
	
	cout << "m_size = " << m_size << " communityInd.size() = " << communityInd.size() << endl; 
	vector<double> m_conList;

	m_conList.assign(m_size, 0.0);
	vector<double> sumCs(communityNum, 0.0);
	vector<double> sumMs(communityNum, 0.0);
	double i_cs = 0.0;
	double i_ms = 0.0;
	
	for(int i = 0; i < communityInd.size(); ++i){
		i_cs = 0.0;
		i_ms = 0.0;
		
		for(int j = 0; j < communityInd.size(); ++j){
			if(communityInd[i] != communityInd[j]){
				i_cs += m_matrix[i][j];
			}else{
				i_ms += m_matrix[i][j];
			}
		}
		
		m_conList[i] = i_cs;
		sumCs[communityInd[i]] += i_cs;
		sumMs[communityInd[i]] += i_ms;
	}
	
	for(int i = 0; i < communityInd.size(); ++i){
		m_conList[i] /= (2 * sumMs[communityInd[i]] + sumCs[communityInd[i]]);
	}
	cout << "haha\n";
	return m_conList;
}*/

//TPR
//for undirected graph : trivial
//for directed graph : make every edge undirected
double Graph::CalcTPRMtrix(const vector<int>& communityInd)
{	
	int numTriad = 0;
	//calculate the number of triad node communityInd[i] participating in
	for(int i = 0; i < communityInd.size(); ++i){
		vector<int> neighbor;
		//find neighbor of communityInd[i]
		for(int j = 0; j < communityInd.size(); ++j){
			if(i != j){
				if(m_matrix[communityInd[i]][communityInd[j]]){
					neighbor.push_back(communityInd[j]);
				}
				else if(m_matrix[communityInd[j]][communityInd[i]]){
					neighbor.push_back(communityInd[j]);	
				}
			}
		}
		//find the number of pair of connected neighbors
		for(int j = 0; j < neighbor.size(); ++j){
			for(int k = j + 1; k < neighbor.size(); ++k){
				if(m_matrix[neighbor[j]][neighbor[k]]){
					++numTriad;
				}
				else if(m_matrix[neighbor[k]][neighbor[j]]){
					++numTriad;	
				}
			}
		}
	}
	return numTriad / communityInd.size();
}

double Graph::CalcInDen(const vector<int>& communityInd)
{	
	double Ms = 0;
	//calculate the number of triad node communityInd[i] participating in
	for(int i = 0; i < communityInd.size(); ++i){
		for(int j = 0; j < communityInd.size(); ++j){
			if(m_matrix[communityInd[i]][communityInd[j]]){
				++Ms;
			}
			if(m_matrix[communityInd[j]][communityInd[i]]){
				++Ms;
			}
		}
	}
	if(communityInd.size() == 0)return 0;
	if(communityInd.size() - 1 == 0)return 0;
	return Ms / (communityInd.size() * (communityInd.size() - 1));
}

double Graph::CalcInDen(const set<int>& communityInd)
{	
	double Ms = 0;
	//calculate the number of triad node communityInd[i] participating in
	for(set<int>::iterator i = communityInd.begin(); i != communityInd.end(); ++i){
		for(set<int>::iterator j = communityInd.begin(); j != communityInd.end(); ++j){
			if(m_matrix[*i][*j]){
				++Ms;
			}
			if(m_matrix[*j][*i]){
				++Ms;
			}
		}
	}
	if(communityInd.size() == 0)return 0;
	if(communityInd.size() - 1 == 0)return 0;
	return Ms / (communityInd.size() * (communityInd.size() - 1));
}

double Graph::InDen()
{	
	double inden = 0;
	//calculate the number of triad node communityInd[i] participating in
	for(size_t i = 0; i < m_communityNumber; ++i){
		double Ms = 0;
		int n = 0;
		for(size_t j = 0; j < m_size; ++j){
			for(size_t k = 0; k < m_size; ++k){
				if(m_communities[j] == i){
					++n;
					if(m_communities[k] == i){
						if(m_matrix[j][k]){
							++Ms;
						}
						if(m_matrix[k][j]){
							++Ms;
						}
					}
				}
			}
		}
		if(n != 1)inden += Ms / (n * (n - 1)) * n / m_size;
	}

	return inden;
}

void Graph::Print() const
{
	cout << "Matrix:" << endl;
	for(int i = 0; i < m_size; ++i)
	{
		for(int j = 0; j < m_size; ++j)
		{
			cout << m_matrix[i][j] << '\t';
		}
		cout << endl;
	}
	cout << "Modularity matrix:" << endl;
	for(int i = 0; i < m_size; ++i)
	{
		for(int j = 0; j < m_size; ++j)
		{
			cout << m_modMatrix[i][j] << '\t';
		}
		cout << endl;
	}
}

void Graph::PrintCommunity(const string& fileName) const
{
	ofstream file(fileName.c_str());
	if(!file.is_open())
		return;
	for(int i = 0; i < m_size; ++i)
		file << m_communities[i] << endl;
	file.close();
}

void Graph::SetCommunities(const vector<int>& new_communities, int number)
{
	if(m_size != new_communities.size())
		return;
	m_communities = new_communities;
	if(number == -1)
		m_communityNumber = *max_element(m_communities.begin(), m_communities.end()) + 1;
	else
		m_communityNumber = number;
}

double Graph::Modularity() const
{
	double mod = 0;
	for(int i = 0; i < m_modMatrix.size(); ++i)
		for(int j = 0; j < m_modMatrix.size(); ++j)
			if(m_communities[i] == m_communities[j])
				mod += m_modMatrix[i][j];
	return mod;
}


void Graph::PerformSplit(int origin, int dest, const vector<int>& split_communities)
{
	if(dest > m_communityNumber)
		dest = m_communityNumber;
	if(dest == m_communityNumber)
		++m_communityNumber;
	for(int i = 0; i < m_size; ++i)
		if(m_communities[i] == origin && split_communities[i])
			m_communities[i] = dest;
}

bool Graph::IsCommunityEmpty(int comm) const
{
	for(int i = 0; i < m_size; ++i)
		if(m_communities[i] == comm)
			return false;
	return true;
}

bool Graph::DeleteCommunityIfEmpty(int comm)
{
	if(IsCommunityEmpty(comm))
	{
		set<int> comms;
        for(int i = 0; i < m_size; ++i)
		{
			if(m_communities[i] > comm)
				--m_communities[i];
			comms.insert(m_communities[i]);
		}
		m_communityNumber = comms.size();
        return true;
	}
	return false;
}

vector<int> Graph::CommunityIndices(int comm) const
{
	vector<int> res;
	for(int i = 0; i < m_size; ++i)
	{
		if(m_communities[i] == comm)
			res.push_back(i);
	}
	return res;
}

vector< vector<double> > Graph::GetModularitySubmatrix(const vector<int>& indices) const
{
	vector< vector<double> > res(indices.size(), vector<double>(indices.size()));
	for(int i = 0; i < indices.size(); ++i)
		for(int j = 0; j < indices.size(); ++j)
			res[i][j] = m_modMatrix[indices[i]][indices[j]];
	return res;
}


vector<double> Graph::GetCorrectionVector(const vector<int>& origCommInd, const vector<int>& destCommInd) const
{
	vector<double> res(origCommInd.size(), 0.0);
	for(int i = 0; i < origCommInd.size(); ++i)
		for(int j = 0; j < destCommInd.size(); ++j)
			res[i] += m_modMatrix[destCommInd[j]][origCommInd[i]];
	return res;
}
