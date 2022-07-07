#include <bits/stdc++.h>
#include <random>
using namespace std;
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());


// The vector model is used to represent a Model of the formula.
// The vector assume is used to keep track of the currently assigned literals.
// The vector literal_count is used to store the frequency of each literal in the formula in a sorted manner.
// The set modelSet stores the literals of the current model.


vector<int> model,assume;
vector< pair<int,int> > literal_count;
set<int> modelSet;

// The vector clauses is used to represent the formula in CNF

vector< vector<int> > clauses;


// Check if literal is present in model
int checkLiteral(int literal){

    if(modelSet.find(literal)!=modelSet.end())
    return 1;
    else
    return 0;

}

// Check if formula is SAT on given model
int checkSAT(int no_of_Clausess){
    
    for(int i=0;i<no_of_Clausess;i++){
        int flag=0;
        for(int j=0;j<clauses[i].size();j++){
            if(checkLiteral(clauses[i][j])){
                flag=1;
                break;
            }
        }
        if(!flag)
        return 0;
    }
    return 1;
}


// Check if formula is UNSAT on given model
int checkUNSAT(int no_of_Clausess){
    
    for(int i=0;i<no_of_Clausess;i++){
        int flag=0;
        for(int j=0;j<clauses[i].size();j++){
            if(!checkLiteral(-clauses[i][j])){
                flag=1;
                break;
            }
        }
        if(!flag)
        return 1;
    }
    return 0;
}

// function to perform unit resolution in a given formula 
// Returns 1 if a model is found at an intermediate step else returns 0
int unitPropagation(int no_of_Clausess, int height){

    int flag=0;
    for(int i=0;i<no_of_Clausess;i++){
        int count=0,index=-1;
        for(int j=0;j<clauses[i].size();j++){
            if(!checkLiteral(-clauses[i][j])){
                count++;
                index=j;
            }
        }
        if(count==1&&!checkLiteral(clauses[i][index])){
            if(checkLiteral(-clauses[i][index]))
            return 0;
            model.push_back(clauses[i][index]);
            modelSet.insert(clauses[i][index]);
            assume[abs(clauses[i][index])] = height;
            flag=1;
        }
    }
    if(flag){
        
        if(checkSAT(no_of_Clausess))
        return 1;
        return unitPropagation(no_of_Clausess,height);
    }
    else{
        if(checkSAT(no_of_Clausess))
        return 1;
        return 0;
    }


}
// function to perform recursive DPLL on given formula
// Returns 1 and generates a model if the formula is satisfiable else returns 0
int SATsolver(int no_of_Var, int no_of_Clausess, int height){

    if(checkSAT(no_of_Clausess))
    return 1;
    else if(checkUNSAT(no_of_Clausess))
    return 0;
    
    // finding the literal which is currently unassigned and has maximum frequency
    int index = -1;
    for(int i=1;i<=no_of_Var;i++){
        if(assume[literal_count[i].second]==0){
            index = literal_count[i].second;
            break;
        }
    }
    
    // assuming the above literal to be assigned true
    model.push_back(index);
    modelSet.insert(index);
    assume[index] = 1;

    // checking on the previous assumptions whether they are unsatisfiable
    if(!checkUNSAT(no_of_Clausess)){
        
        // applying unit propagation on the formula with the current assumptions
        int flag = unitPropagation(no_of_Clausess,height);
        if(flag==1)
        return 1; 
        
        int flag2 = SATsolver(no_of_Var,no_of_Clausess,height+1);
        if(flag2)
        return 1;
        
        for(int i=model.size()-1;i>=0;i--){
            if(assume[abs(model[i])]==height){
                assume[abs(model[i])]=0;
                modelSet.erase(model[i]);
                model.pop_back();
            }else break;
        }
        
    }
    model.pop_back();
    modelSet.erase(index);
    
    // now assuming the literal to be assigned false
    model.push_back(-index);
    modelSet.insert(-index);
    assume[index] = 1;

    // checking on the previous assumptions whether they are unsatisfiable
    if(!checkUNSAT(no_of_Clausess)){
        
        // applying unit propagation on the formula with the current assumptions
        int flag = unitPropagation(no_of_Clausess,height);
        if(flag==1)
        return 1; 
        
        int flag2 = SATsolver(no_of_Var,no_of_Clausess,height+1);
        if(flag2)
        return 1;
        for(int i=model.size()-1;i>=0;i--){
            if(assume[abs(model[i])]==height){
                assume[abs(model[i])]=0;
                modelSet.erase(model[i]);
                model.pop_back();
            }else break;
        }
    }
    model.pop_back();
    modelSet.erase(-index);
    assume[index]=0;
    return 0;

}


int main(){

    cout<<"Enter input file path : ";
    string filename;
    cin>>filename;
    int siz = filename.size();
    char ch[siz];
    for(int i =0;i<siz;i++)
    {
        ch[i]=filename[i];
    }
    freopen(ch,"r",stdin);
    freopen("output.txt","w",stdout);
    
    char c;
    cin>>c;
    string s;
    while(c=='c'){
        getline(cin,s);
        cin>>c;
    }
    cin>>s;
    int no_of_Var, no_of_Clauses;
    cin>>no_of_Var>>no_of_Clauses;

    for(int i=0;i<=no_of_Var;i++){
        assume.push_back(0);
        literal_count.push_back(make_pair(0,i));
    }
    for(int i=0;i<no_of_Clauses;i++){
        vector<int> v;
        for(int j=0;;j++){
            int a;
            cin>>a;
            if(a==0)
            break;
            v.push_back(a);
            literal_count[abs(a)].first++;
        }
        clauses.push_back(v);
    }
    
    // Sorting the literals in decreasing order of their frequency in the formula
    sort(literal_count.rbegin(),literal_count.rend());
    
    int satisfiable = SATsolver(no_of_Var,no_of_Clauses,10);

    if(satisfiable){
        cout<<"Formula is satisfiable"<<endl;

        for(int i=1;i<=no_of_Var;i++){
            if(checkLiteral(i))
            cout<<i<<" ";
            else cout<<-i<<" ";
        }
        cout<<"\n";
        
    }else{
        cout<<"Formula is unsatisfiable\n";
    }
    
    cout<<"Time:"<<1000*((double)clock())/(double)CLOCKS_PER_SEC<<"ms\n";
    return 0;
}