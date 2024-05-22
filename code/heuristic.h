#ifndef _HEURISTIC_H_
#define _HEURISTIC_H_

#include "basis_pms.h"
#include "deci.h"
#include <limits>
#include <assert.h>

void ISDist::init(vector<int> &init_solution)
{
    soft_large_weight_clauses_count = 0;
    if (1 == problem_weighted) // weighted partial MaxSAT
    {
        if (0 != num_hclauses)
        {
            if ((0 == local_soln_feasible || 0 == best_soln_feasible))
            {
                for (int c = 0; c < num_clauses; c++)
                {
                    already_in_soft_large_weight_stack[c] = 0;
                    clause_selected_count[c] = 0;
                    clause_weight[c] = 1;
                }
            }
            else
            {
                for (int c = 0; c < num_clauses; c++)
                {
                    already_in_soft_large_weight_stack[c] = 0;
                    clause_selected_count[c] = 0;

                    if (org_clause_weight[c] == top_clause_weight)
                        clause_weight[c] = 1;
                    else
                    {
                        clause_weight[c] = tuned_org_clause_weight[c];
                        if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
                        {
                            already_in_soft_large_weight_stack[c] = 1;
                            soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                        }
                    }
                }
            }
        }
        else
        {
            for (int c = 0; c < num_clauses; c++)
            {
                already_in_soft_large_weight_stack[c] = 0;
                clause_selected_count[c] = 0;
                clause_weight[c] = tuned_org_clause_weight[c];
                if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
                {
                    already_in_soft_large_weight_stack[c] = 1;
                    soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                }
            }
        }
    }
    else // unweighted partial MaxSAT
    {
        for (int c = 0; c < num_clauses; c++)
        {
            already_in_soft_large_weight_stack[c] = 0;
            clause_selected_count[c] = 0;

            if (org_clause_weight[c] == top_clause_weight)
                clause_weight[c] = 1;
            else
            {
                if ((0 == local_soln_feasible || 0 == best_soln_feasible) && num_hclauses > 0)
                {
                    clause_weight[c] = 1;
                }
                else
                {
                    clause_weight[c] = coe_soft_clause_weight;
                    if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
                    {
                        already_in_soft_large_weight_stack[c] = 1;
                        soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                    }
                }
            }
        }
    }

    if (init_solution.size() == 0)
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = init_solution[v];
            if (cur_soln[v] != 0 && cur_soln[v] != 1)
                cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    local_soln_feasible = 0;
    // init stacks
    hard_unsat_nb = 0;
    soft_unsat_weight = 0;
    hardunsat_stack_fill_pointer = 0;
    softunsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;
    large_weight_clauses_count = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for (int c = 0; c < num_clauses; ++c)
    {
        sat_count[c] = 0;
        for (int j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
        {
            unsat(c);
        }
    }

    /*figure out score*/
    for (int v = 1; v <= num_vars; v++)
    {
        if(fixed[v]){
            score[v] = DOUBEL_MIN;
            continue;
        }
        score[v] = 0.0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            int c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v] += clause_weight[c];
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v] -= clause_weight[c];
        }
    }

    // init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (int v = 1; v <= num_vars; v++)
    {
        if (score[v] > 0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }
}

int ISDist::pick_var(SOL_TANK* tank)
{
    int i, v, c, pos;
    int best_var;
    int sel_c;
    lit *p;

    if (goodvar_stack_fill_pointer > 0)
    {
        int best_array_count = 0;
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
            return goodvar_stack[rand() % goodvar_stack_fill_pointer];

        if (goodvar_stack_fill_pointer < hd_count_threshold)
        {
            best_var = goodvar_stack[0];

            for (i = 1; i < goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            return best_var; // best_array[rand() % best_array_count];
        }
        else
        {
            best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];

            for (i = 1; i < hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            return best_var; // best_array[rand() % best_array_count];
        }
    }
   
    update_clause_weights();
    bool clauses_update = false;
    
    #if VOTING_IN_SEARCH
        // if(!best_soln_feasible){
            pos = tank -> push_try_into_tank(cur_soln, hardunsat_stack_fill_pointer, soft_unsat_weight);
            tank -> push_clauses_states(hardunsat_stack, softunsat_stack, hardunsat_stack_fill_pointer, softunsat_stack_fill_pointer, pos);
        
            
        // }
        // if(tank -> num_in_tries_tank > 0 && !best_soln_feasible){
            if(tank -> num_in_tries_tank > 0){
                sample_num = 0;
                if(hardunsat_stack_fill_pointer > 0){
                    if(hardunsat_stack_fill_pointer < Max_Sample_Num){
                        // for(int i = 0;i < hardunsat_stack_fill_pointer;i++){
                        //     sample_unsat_clauses[i] = hardunsat_stack[i];
                        //     sample_clause_weight[i] = clause_weight[hardunsat_stack[i]];
                        // }
                        // sample_num = hardunsat_stack_fill_pointer;

                        // c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
                        // sample_clause_weight[sample_num] = clause_weight[c];
                        // sample_unsat_clauses[sample_num++] = c;
                    }
                    else{
                        for(int i = 0;i < Max_Sample_Num;i++){
                            c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
                            if(!clause_in_sample[c])
                            {
                                clause_in_sample[c] = 1;
                                sample_clause_weight[sample_num] = clause_weight[c];
                                sample_unsat_clauses[sample_num++] = c;
                            }
                        }
                        for(int i = 0;i < sample_num;i++){
                            clause_in_sample[sample_unsat_clauses[i]] = 0;
                        }
                    }
                }
                
            }
            
            pos = tank ->calc_fitness_ret_pos(sample_unsat_clauses, sample_num, sample_clause_weight);
            int learn_clauses = 0;
            int flip_var_nums = 0;
            // printf("before flip unsat clauses: %d\n", hard_unsat_nb);
            for(int i = 0;i < sample_num;i++){
                c = sample_unsat_clauses[i];
                lit* p = clause_lit[c];
                if(tank -> clauses_states[pos][c]){
                    for(int v = p -> var_num; (v = p -> var_num) != 0; p++){   
                        if(cur_soln[v] != tank -> tries_tank[pos][v]){
                            flip(v);
                            time_stamp[v] = step;
                            flip_var_nums += 1;
                        }  
                    }
                    
                    learn_clauses += 1; 
                    clauses_update = true;
                }    
            }
            
            // printf("after flip unsat clauses: %d\n", hard_unsat_nb);
            // if(sample_num > 0){
            //     printf("sample num: %d, learn_clauses:%d, flip_var_nums:%d\n", sample_num, learn_clauses, flip_var_nums);
            // }     
            // if(learn_clauses == 0){
            //     printf("pos: %d\n", pos);
            // }
        
    #endif
    
    if(!clauses_update){
        if (hardunsat_stack_fill_pointer > 0)
        {
            sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        }
        else
        {
            sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
        }
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob){
            int tmp_cnt = 0;
            int random_v = clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
            while(fixed[random_v]){
                if(tmp_cnt >= clause_lit_count[sel_c]){
                    if (hardunsat_stack_fill_pointer > 0)
                    {
                        sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
                    }
                    else
                    {
                        sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
                    }
                    tmp_cnt = 0;
                }
                random_v = clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
                tmp_cnt ++;
            }
            
            return random_v;
        }
        best_var = clause_lit[sel_c][0].var_num;
        p = clause_lit[sel_c];
        for (p++; (v = p->var_num) != 0; p++)
        {
            if (score[v] > score[best_var])
                best_var = v;
            else if (score[v] == score[best_var])
            {
                if (time_stamp[v] < time_stamp[best_var])
                    best_var = v;
            }
        }
        return best_var;
    }
    else{
        return -1;
    }

}

int ISDist::pick_var()
{
    int i, v;
    int best_var;
    int sel_c;
    lit *p;

    if (goodvar_stack_fill_pointer > 0)
    {
        int best_array_count = 0;
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
        {
            int test_v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
            return test_v;
        }
        if (goodvar_stack_fill_pointer < hd_count_threshold)
        {
            best_var = goodvar_stack[0];

            for (i = 1; i < goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            
            return best_var; // best_array[rand() % best_array_count];
        }
        else
        {
            best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];

            for (i = 1; i < hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
           
            return best_var; // best_array[rand() % best_array_count];
        }
    }

    update_clause_weights();

    if (hardunsat_stack_fill_pointer > 0)
    {
        sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
    }
    else
    {
        sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
    }
    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob){
        int tmp_cnt = 0;
        int random_v = clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
        while(fixed[random_v]){
            if(tmp_cnt >= clause_lit_count[sel_c]){
                if (hardunsat_stack_fill_pointer > 0)
                {
                    sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
                }
                else
                {
                    sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
                }
                tmp_cnt = 0;
            }
            random_v = clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
            tmp_cnt ++;
        }
        return random_v;
    }
        

    best_var = clause_lit[sel_c][0].var_num;
    p = clause_lit[sel_c];
    for (p++; (v = p->var_num) != 0; p++)
    {
        if (score[v] > score[best_var])
            best_var = v;
        else if (score[v] == score[best_var])
        {
            if (time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
    }
    return best_var;
}

void ISDist::local_search_with_decimation(char *inputfile)
{
    if (1 == problem_weighted)
    {
        if (total_soft_length / num_sclauses > 100)
        {
            //cout << "c avg_soft_length: " << total_soft_length / num_sclauses << endl;
            h_inc = 300;
            s_inc = 100;
        }
        if (0 != num_hclauses)
        {
            coe_tuned_weight = (double)(coe_soft_clause_weight * num_sclauses) / double(top_clause_weight - 1);
            for (int c = 0; c < num_clauses; c++)
            {
                if (org_clause_weight[c] != top_clause_weight)
                {
                    tuned_org_clause_weight[c] = (double)org_clause_weight[c] * coe_tuned_weight;
                }
            }
        }
        else
        {
            softclause_weight_threshold = 0;
            soft_smooth_probability = 1E-3;
            hd_count_threshold = 22;
            rdprob = 0.036;
            rwprob = 0.48;
            s_inc = 1.0;
            for (int c = 0; c < num_clauses; c++)
            {
                tuned_org_clause_weight[c] = org_clause_weight[c];
            }
        }
    }
    else
    {
        if (0 == num_hclauses)
        {
            hd_count_threshold = 94;
            coe_soft_clause_weight = 397;
            rdprob = 0.007;
            rwprob = 0.047;
            soft_smooth_probability = 0.002;
            softclause_weight_threshold = 550;
        }
    }
    Decimation deci(var_lit, var_lit_count, clause_lit, org_clause_weight, top_clause_weight);
    deci.make_space(num_clauses, num_vars);

    #if VOTING_IN_SEARCH || VOTING_IN_UNIT_PROCESS
    int c;
    SOL_TANK* tank = new SOL_TANK(num_vars, num_clauses, fixed);
    
    tank->init();
    #endif

    opt_unsat_weight = __LONG_LONG_MAX__;
    for (tries = 1; tries < max_tries; ++tries)
    {
        deci.init(local_opt_soln, best_soln, unit_clause, unit_clause_count, clause_lit_count);
        #if VOTING_IN_UNIT_PROCESS
        deci.unit_prosess(tank);
        #else
        deci.unit_prosess();
        #endif

        init(deci.fix);
        
        long long local_opt = __LONG_LONG_MAX__;
        max_flips = max_non_improve_flip;
        for (step = 1; step < max_flips; ++step)
        {
            if (hard_unsat_nb == 0)
            {
                local_soln_feasible = 1;
                if (local_opt > soft_unsat_weight)
                {
                    local_opt = soft_unsat_weight;
                    max_flips = step + max_non_improve_flip;
                }
                if (soft_unsat_weight < opt_unsat_weight)
                {
                    opt_time = get_runtime();
                    //cout << "o " << soft_unsat_weight << " " << total_step << " " << tries << " " << soft_smooth_probability << " " << opt_time << endl;
                    //cout << "o " << soft_unsat_weight << " " << opt_time << endl;
                    opt_unsat_weight = soft_unsat_weight;
                    #if VOTING_IN_SEARCH || VOTING_IN_UNIT_PROCESS
                        tank->push_sol_into_tank(cur_soln);
                    #endif
                    
                    // for (int v = 1; v <= num_vars; ++v)
                    //     best_soln[v] = cur_soln[v];
                    // if (opt_unsat_weight <= best_known)
                    // {
                        // cout << "c best solution found." << endl;
                        // if (opt_unsat_weight < best_known)
                        // {
                        //     cout << "c a better solution " << opt_unsat_weight << endl;
                        // }
                    //     return;
                    // }
                }
                if (best_soln_feasible == 0)
                {
                    best_soln_feasible = 1;
                    // break;
                }
            }
            // if(goodvar_stack_fill_pointer==0) cout<<step<<": 0"<<endl;
            /*if (step % 1000 == 0)
            {
                double elapse_time = get_runtime();
                if (elapse_time >= cutoff_time)
                    return;
                else if (opt_unsat_weight == 0)
                    return;
            }*/
            int flipvar;
            #if VOTING_IN_SEARCH
            // not reach local optimal or cur sol is a feasible sol or no history record
                
                flipvar = pick_var(tank);
                if(flipvar != -1){
                    flip(flipvar);
                    time_stamp[flipvar] = step;
                }
            #else
                flipvar = pick_var();
                flip(flipvar);
                time_stamp[flipvar] = step;
            #endif
            
            
            total_step++;
        }

    }
}

void ISDist::hard_increase_weights()
{
    int i, c, v;
    for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c = hardunsat_stack[i];
        clause_weight[c] += h_inc;

        if (clause_weight[c] == (h_inc + 1))
            large_weight_clauses[large_weight_clauses_count++] = c;

        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            if(fixed[v])continue;
            score[v] += h_inc;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
    return;
}

void ISDist::soft_increase_weights()
{
    int i, c, v;

    if (1 == problem_weighted)
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_weight[c] >= tuned_org_clause_weight[c] + softclause_weight_threshold)
                continue;
            else
                clause_weight[c] += s_inc;

            if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                if(fixed[v])continue;
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    else
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_weight[c] >= coe_soft_clause_weight + softclause_weight_threshold)
                continue;
            else
                clause_weight[c] += s_inc;

            if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                if(fixed[v])continue;
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::hard_smooth_weights()
{
    int i, clause, v;
    for (i = 0; i < large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= h_inc;

            if (clause_weight[clause] == 1)
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                if(fixed[v])continue;
                score[v] += h_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::soft_smooth_weights()
{
    int i, clause, v;

    for (i = 0; i < soft_large_weight_clauses_count; i++)
    {
        clause = soft_large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= s_inc;
            if (clause_weight[clause] <= s_inc && already_in_soft_large_weight_stack[clause] == 1)
            {
                already_in_soft_large_weight_stack[clause] = 0;
                soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                if(fixed[v])continue;
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::update_clause_weights()
{
    if (num_hclauses > 0)
    {
        // update hard clause weight
        if (1 == local_soln_feasible && ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && large_weight_clauses_count > large_clause_count_threshold)
        {
            hard_smooth_weights();
        }
        else
        {
            hard_increase_weights();
        }

        // update soft clause weight
        // if (1 == local_soln_feasible && ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
        if (soft_unsat_weight >= opt_unsat_weight)
        {
            if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
            {
                soft_smooth_weights();
            }
            else if (0 == hard_unsat_nb)
            {
                soft_increase_weights();
            }
        }
    }
    else
    {
        if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
        {
            soft_smooth_weights();
        }
        else
        {
            soft_increase_weights();
        }
    }
}

#endif
