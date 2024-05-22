#ifndef SOL_TANK_ 
#define SOL_TANK_

#define VOTING_IN_SEARCH true
#define VOTING_IN_UNIT_PROCESS true

#include <stdlib.h>
#include <vector>

class SOL_TANK{
public:
    SOL_TANK(int num_vars, int num_clauses, int* fixed);
    void push_sol_into_tank(int* sol);
    int  push_try_into_tank(int* tryn, int cur_unsat_clauses, int cur_unsat_weight);
    void push_clauses_states(int* hardunsat_stack, int* softunsat_stack, int hardunsat_stack_fill_pointer, int softunsat_stack_fill_pointer, int pos);
    void free_memory();
    void init();
    int  vote(int);
    bool x(std::vector<int>& fix);
    bool try_x(std::vector<int>& fix);
    bool select_x(std::vector<int>& fix);
    int  calc_fitness_ret_pos(int* sample_clauses, int sample_num, double* clause_weight);
    int  cmp_hardunsat_stack(int* hardunsat_stack, int hardunsat_stack_fill_pointer);
    void print_try_tank();
    bool check_diversity(int* tryn);

    static const int SOL_TANK_SIZE = 1;
    static const int TRIES_TANK_SIZE = 1;
    int epsilon;
    int* sol_tank[SOL_TANK_SIZE];
    int* tries_tank[TRIES_TANK_SIZE];
    int diff_cnt[TRIES_TANK_SIZE];
    int* clauses_states[TRIES_TANK_SIZE];
    int  unsat_clauses_num[TRIES_TANK_SIZE];
    int  unsat_weight[TRIES_TANK_SIZE];
    int* fixed;
    int num_in_tries_tank;
    int num_in_tank;
    int num_clause_states;
    int worst_p;
    int first_try;
    int num_vars;
    int num_clauses;
    int clause_states_beg;
    int min_diff;
    int max_diff;
    int diff[TRIES_TANK_SIZE][TRIES_TANK_SIZE];
};

SOL_TANK::SOL_TANK(int num_vars, int num_clauses, int* fixed):num_vars(num_vars), num_clauses(num_clauses), fixed(fixed){
    for(int i = 0;i < SOL_TANK_SIZE;i++){
        sol_tank[i] = new int[num_vars + 1];
    }
    for(int i = 0;i < TRIES_TANK_SIZE;i++){
        tries_tank[i] = new int[num_vars + 1];
        clauses_states[i] = new int[num_clauses + 1];
    }

    epsilon = 10;
    num_clause_states = 0;
    num_in_tries_tank = 0;
    num_in_tank = 0;
    worst_p = 0;
    first_try = 0;
    clause_states_beg = 0;
};

void SOL_TANK::init(){
    
}

void SOL_TANK::push_sol_into_tank(int* sol){
    if(num_in_tank < SOL_TANK_SIZE){
        for(int i = 1;i <= num_vars;i++){
            sol_tank[num_in_tank][i] = sol[i];
        }
        num_in_tank ++;
    }
    else{
        for(int i = 1;i <= num_vars;i++){
            sol_tank[worst_p][i] = sol[i];
        }
        worst_p = (worst_p + 1) % SOL_TANK_SIZE;
    }
}

bool SOL_TANK::check_diversity(int* tryn)
{
    int test_v = rand() % num_vars + 1;
    int test_num = 100;
    bool isDiverse = true;
    for(int i = 0;i < num_in_tries_tank;i++)diff_cnt[i] = 0;

    for(int i = 1;i < test_num;i++){
        for(int j = 0;j < num_in_tries_tank;j++){
            if(tryn[test_v] != tries_tank[j][test_v])diff_cnt[j] += 1;
        }
        test_v = rand() % num_vars + 1;
    }
    
    for(int i = 0;i < num_in_tries_tank;i++)
    {
        if(diff_cnt[i] == 0)isDiverse = false;
    }
    return isDiverse;
}

int SOL_TANK::push_try_into_tank(int* tryn, int cur_unsat_clauses, int cur_unsat_weight){
    int i;

    if(num_in_tries_tank < TRIES_TANK_SIZE){
        for(i = 1;i <= num_vars;i++){
            tries_tank[num_in_tries_tank][i] = tryn[i];
        }
        unsat_clauses_num[num_in_tries_tank] = cur_unsat_clauses;
        unsat_weight[num_in_tries_tank] = cur_unsat_weight;
        num_in_tries_tank ++;
        return num_in_tries_tank - 1;
    }
    else{
        int to_replace = -1;
        int to_replace_unsat_num = cur_unsat_clauses;
        int to_replace_unsat_weight = cur_unsat_weight;
        // if(check_diversity(tryn)){
            for(i = 0;i < num_in_tries_tank;i++){
                if(unsat_clauses_num[i] > to_replace_unsat_num){
                    to_replace = i;
                    to_replace_unsat_num = unsat_clauses_num[i];
                    to_replace_unsat_weight = unsat_weight[i];
                }
                else if(unsat_clauses_num[i] == to_replace_unsat_num){
                    if(to_replace_unsat_weight <= unsat_weight[i]){
                        to_replace = i;
                        to_replace_unsat_num = unsat_clauses_num[i];
                        to_replace_unsat_weight = unsat_weight[i];
                    }
                }
            }
            if(to_replace != -1){
                for(i = 1;i <= num_vars;i++){
                    tries_tank[to_replace][i] = tryn[i];
                }
                unsat_clauses_num[to_replace] = cur_unsat_clauses;
                unsat_weight[to_replace] = cur_unsat_weight;
            }    
        // }
        return to_replace;
    }
}

void SOL_TANK::free_memory(){
    #if VOTING_IN_UNIT_PROCESS || VOTING_IN_SEARCH
    for(int i = 0;i < SOL_TANK_SIZE;i++){
        delete sol_tank[i];
    }
    #endif
}

int SOL_TANK::vote(int v){
    if(num_in_tank == 0){
        return rand() % 2;
    }
    int cnt_0 = 0;
    for(int i = 0;i < num_in_tank;i++){
        if(sol_tank[i][v] == 0){
            cnt_0 ++;
        }
    }
    int vote_num = rand() % num_in_tank;
    if(vote_num < cnt_0)return 0;
    else return 1;
}

bool SOL_TANK::x(std::vector<int>& fix){
    if(num_in_tank == 0)return false;
    int i, rand_num, v = 1, cnt_0 = 0;
    for(;v <= num_vars; v++){
        if(fixed[v]){
            fix[v] = sol_tank[0][v];
            continue;
        }
        cnt_0 = 0;
        for(i = 0;i < num_in_tank;i++){
            if(sol_tank[i][v] == 0){
                cnt_0 ++;
            }
        }
        rand_num = rand() % 100;
        if(rand_num >= epsilon){
            fix[v] = (cnt_0 > num_in_tank - cnt_0 ? 0 : 1);
        }
        else{
            fix[v] = (cnt_0 > num_in_tank - cnt_0 ? 1 : 0);
        }
    }
    return true;
}

bool SOL_TANK::try_x(std::vector<int>& fix){
    if(num_in_tries_tank == 0)return false;
    int i, rand_num, v = 1, cnt_0 = 0;
    for(;v <= num_vars; v++){
        if(fixed[v]){
            fix[v] = tries_tank[0][v];
            continue;
        }
        cnt_0 = 0;
        for(i = 0;i < num_in_tank;i++){
            if(tries_tank[i][v] == 0){
                cnt_0 ++;
            }
        }
        rand_num = rand() % 100;
        if(rand_num >= epsilon){
            fix[v] = (cnt_0 > num_in_tries_tank - cnt_0 ? 0 : 1);
        }
        else{
            fix[v] = (cnt_0 > num_in_tries_tank - cnt_0 ? 1 : 0);
        }
    }
    return true;
}

bool SOL_TANK::select_x(std::vector<int>& fix){
    if(num_in_tank == 0)return try_x(fix);
    else{
        // return x(fix);
        return false;
    }
}

void SOL_TANK::push_clauses_states(int* hardunsat_stack, int* softunsat_stack, int hardunsat_stack_fill_pointer, int softunsat_stack_fill_pointer, int pos){
    if(pos == -1)return;
    int i;
    for(i = 0;i < num_clauses;i++){
        clauses_states[pos][i] = 1;
    }
    for(i = 0;i < hardunsat_stack_fill_pointer;i++){
        clauses_states[pos][hardunsat_stack[i]] = 0;
    }
    for(i = 0;i < softunsat_stack_fill_pointer;i++){
        clauses_states[pos][softunsat_stack[i]] = 0;
    }
}

int SOL_TANK::calc_fitness_ret_pos(int* sample_clauses, int sample_num, double* clause_weight){
    int i, j, fitness = 0;
    int best_pos, best_fitness;
    for(i = 0;i < sample_num;i++)
    {
        if(clauses_states[0][sample_clauses[i]])fitness += clause_weight[i];
    }
    best_pos = 0;
    best_fitness = fitness;
    
    for(int pos = 1;pos < num_in_tries_tank;pos++){
        fitness = 0;
        for(i = 0;i < sample_num;i++)
        {
            if(clauses_states[pos][sample_clauses[i]])fitness += clause_weight[i];
        }
        if(fitness > best_fitness){
            best_fitness = fitness;
            best_pos = pos;
        }
    }
    return best_pos;
}

int SOL_TANK::cmp_hardunsat_stack(int* hardunsat_stack, int hardunsat_stack_fill_pointer){
    if(num_clause_states == 0)return -1;
    int c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
    int cnt = 0;
    while(clauses_states[clause_states_beg][c] == 0){
        c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        cnt++;
        if(cnt >= hardunsat_stack_fill_pointer)break;
    }
    if(clauses_states[clause_states_beg][c] == 0)return -1;
    else return c;
}

void SOL_TANK::print_try_tank(){
    printf("unsat clauses: ");
    for(int i = 0;i < num_in_tries_tank;i++){
        printf("%d ", unsat_clauses_num[i]);
    }
    printf("\nunsat weights: ");
    for(int i = 0;i < num_in_tries_tank;i++){
        printf("%d ", unsat_weight[i]);
    }
    printf("\n");
}

#endif
