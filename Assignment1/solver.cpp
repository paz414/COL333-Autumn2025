#include "solver.h"
#include <iostream>
#include <chrono>
#include <unordered_map>
#include <random>
#include <algorithm>
#include <limits>

using namespace std;
using namespace chrono;
#define pb push_back


static unordered_map<int,int> getHelicopterIndex;
static unordered_map<int,int> getVillageIndex;

static void FillIndices(const ProblemData& problem){
    getHelicopterIndex.clear();
    getVillageIndex.clear();
    for (int i = 0; i < (int)problem.helicopters.size(); ++i)
        getHelicopterIndex[problem.helicopters[i].id] = i;
    for(int i=0;i<(int)problem.villages.size();i++)
        getVillageIndex[problem.villages[i].id]=i;
}

static int heliIdxById(int id){
    auto it = getHelicopterIndex.find(id);
    return it == getHelicopterIndex.end() ? -1 : it->second;
}
static int villIdxById(int id){
    auto it = getVillageIndex.find(id);
    return it == getVillageIndex.end() ? -1 : it->second;
}

// --- trip metrics ---
static double tripWeight(const ProblemData& p, const Trip& t){
    return t.dry_food_pickup        * p.packages[0].weight +
           t.perishable_food_pickup * p.packages[1].weight +
           t.other_supplies_pickup  * p.packages[2].weight;
}
static double tripDistanceFor(const ProblemData& p, int heli_idx, const Trip& t){
    const Point& home = p.cities[p.helicopters[heli_idx].home_city_id-1];
    Point cur = home;
    double d = 0.0;
    for (const auto& drop : t.drops){
        int vi = villIdxById(drop.village_id);
        d += ::distance(cur, p.villages[vi].coords);
        cur = p.villages[vi].coords;
    }
    d += ::distance(cur, home);
    return d;
}
// --- keep pickup fields consistent with drops ---
static void syncPickups(Trip& t){
    int d = 0, pr = 0, o = 0;
    for (const auto& x : t.drops){
        d  += x.dry_food;
        pr += x.perishable_food;
        o  += x.other_supplies;
    }
    t.dry_food_pickup        = d;
    t.perishable_food_pickup = pr;
    t.other_supplies_pickup  = o;
}

// --- feasibility checks ---
static bool tripFeasible(const ProblemData& p, int heli_idx, const Trip& t){
    const auto& h = p.helicopters[heli_idx];
    if (tripWeight(p, t) > h.weight_capacity) return false;
    if (tripDistanceFor(p, heli_idx, t) > h.distance_capacity) return false;
    return true;
}
static bool planFeasible(const ProblemData& p, const HelicopterPlan& plan){
    int helicopterIndex = heliIdxById(plan.helicopter_id);
    if (helicopterIndex < 0) return false;
    double sum = 0.0;
    for (const auto& t : plan.trips){
        if (!t.drops.empty()){
            if (!tripFeasible(p, helicopterIndex, t)) return false;
            sum += tripDistanceFor(p, helicopterIndex, t);
        }
    }
    return sum <= p.d_max;
}
static bool solutionFeasible(const ProblemData& p, const Solution& sol){
    for (const auto& plan : sol)
        if (!planFeasible(p, plan)) return false;
    return true;
}

static void repairPlan(const ProblemData& p, HelicopterPlan& plan){
    int helicopterIndex = heliIdxById(plan.helicopter_id);
    if (helicopterIndex < 0) return;
    const auto& h = p.helicopters[helicopterIndex];

    double used = 0.0;
    vector<Trip> kept;
    for (auto t : plan.trips){
        if (t.drops.empty()) continue;
        syncPickups(t);
        double td = tripDistanceFor(p, helicopterIndex, t);
        if (tripWeight(p, t) <= h.weight_capacity &&
            td <= h.distance_capacity &&
            used + td <= p.d_max)
        {
            kept.push_back(std::move(t));
            used += td;
        }
    }
    plan.trips.swap(kept);
}

static void repairSolution(const ProblemData& p, Solution& sol){
    for (auto& plan : sol) repairPlan(p, plan);
}


/* 
Starting off with a simple solution.
We need to find a single village within the helicopters reach
Trip being performed = home_city --> village --> home_city
The constraint are d_cap and D_max*/
int greedyFind(int city_id, int helicopter_index, const ProblemData &problem, vector<pair<int,int>>& villageNeeds, double HelicopterDistanceCap, double remainD, int &preferredMealType){
    //WEIGHTS
    double weight_dry = problem.packages[0].weight;
    double weight_perish = problem.packages[1].weight;
    double weight_other = problem.packages[2].weight;
    //VALUES
    double value_dry= problem.packages[0].value;
    double value_perish = problem.packages[1].value;
    double value_other = problem.packages[2].value;

    double ratio_dry = value_dry/weight_dry;
    double ratio_perish = value_perish/weight_perish;

    preferredMealType = (ratio_perish >= ratio_dry)? 1:0; //1 -> perishabled 0-> dry

    int bestVillage = -1;
    double bestScore = 0;

    for (int village=0; village<problem.villages.size();village++){
        if (villageNeeds[village].first <=0 && villageNeeds[village].second <=0) continue;

        double roundTrip = 2.0 * ::distance(problem.cities[city_id-1],problem.villages[village].coords);
        if (roundTrip > HelicopterDistanceCap || roundTrip > remainD) continue;
        
        double WeightLeft = problem.helicopters[helicopter_index].weight_capacity;
        int MealDemand = villageNeeds[village].first;
        int OtherDemand = villageNeeds[village].second;
        
        double valueNet = 0;

        auto pick= [&](double weight,double value,int &MealTemp){
            if(weight <=0) return;
            int canCarry = (int)floor(WeightLeft/weight);
            int carried = min(canCarry,MealTemp);

            valueNet+= carried*value;
            WeightLeft-= carried*weight;
            MealTemp-=carried;
        };
        if(preferredMealType==1) {//1 -> perishable
            pick(weight_perish,value_perish,MealDemand);
            pick(weight_dry,value_dry,MealDemand);
        }
        else{
            pick(weight_dry,value_dry,MealDemand);
            pick(weight_perish,value_perish,MealDemand);
        }

        if ( WeightLeft >0 && OtherDemand>0){

            int canCarry = floor(WeightLeft/weight_other);
            int carried = min(canCarry,OtherDemand);
            valueNet+= carried*value_other;
        }
        double tripCost = problem.helicopters[helicopter_index].fixed_cost+ problem.helicopters[helicopter_index].alpha * roundTrip;
        double score = (valueNet-tripCost)/roundTrip;
        if(score>bestScore){
            bestScore=score;
            bestVillage = village;
        }
    }
    return bestVillage;

}

double evaluateSolution(const ProblemData& problem,const Solution& solution) {
    const double valueDry  = problem.packages[0].value;
    const double valuePer  = problem.packages[1].value;
    const double valueOth  = problem.packages[2].value;

    const int numVillages = (int)problem.villages.size();

    vector<int> deliveredDry(numVillages, 0);
    vector<int> deliveredPer(numVillages, 0);
    vector<int> deliveredOth(numVillages, 0);

    double totalCost  = 0.0;
    double totalValue = 0.0;

    for (const auto& heliPlan : solution) {
        int hIndex = heliIdxById(heliPlan.helicopter_id);
        if (hIndex<0) continue;

        const auto& heli = problem.helicopters[hIndex];
        const Point& homeCity = problem.cities[heli.home_city_id-1]; 

        for (const auto& trip : heliPlan.trips) {
            if (trip.drops.empty()) continue;

            Point currentPos = homeCity;
            double tripDistance = 0.0;

            for (const auto& drop : trip.drops) {
                int vIndex = villIdxById(drop.village_id);
                if (vIndex <0) continue; 

                const Point& villagePos = problem.villages[vIndex].coords;

                tripDistance += ::distance(currentPos, villagePos);
                currentPos = villagePos;

                deliveredDry[vIndex] += drop.dry_food;
                deliveredPer[vIndex] += drop.perishable_food;
                deliveredOth[vIndex] += drop.other_supplies;
            }

            tripDistance += ::distance(currentPos, homeCity);
            totalCost += heli.fixed_cost + heli.alpha * tripDistance;
        }
    }

    for (int vIndex = 0; vIndex < numVillages; ++vIndex) {
        int population = problem.villages[vIndex].population;

        int mealCapacity = 9 * population;
        int otherCapacity = population;

        int servedPer = min(deliveredPer[vIndex], mealCapacity);
        int remainingMealCap = mealCapacity - servedPer;

        int servedDry = min(deliveredDry[vIndex], remainingMealCap);
        int servedOth = min(deliveredOth[vIndex], otherCapacity);

        totalValue += servedPer * valuePer 
                    + servedDry * valueDry 
                    + servedOth * valueOth;
    }

    return totalValue - totalCost;
}

static Solution generate_initial_solution(const ProblemData &problem){
    Solution solution;
    //WEIGHTS
    double weight_dry = problem.packages[0].weight;
    double weight_perish = problem.packages[1].weight;
    double weight_other = problem.packages[2].weight;
    
    //DEMANDS FOR MEALS AND OTHERS
    vector<pair<int,int>> villageNeeds(problem.villages.size()); // <meal,other>
    //Populating demands
    for(int village =0; village<(int)problem.villages.size(); village++){
        int n = problem.villages[village].population;
        villageNeeds[village].first = 9*n; // dry + perish
        villageNeeds[village].second = n; //other
    }
    for(int h=0; h<(int)problem.helicopters.size();h++){
        auto current_helicopter = problem.helicopters[h];
        HelicopterPlan helPlan;
        helPlan.helicopter_id = current_helicopter.id;

        double remainingDistance = problem.d_max;
            
        int homeCity = current_helicopter.home_city_id;
        double distanceCap = current_helicopter.distance_capacity;
        double weightCap = current_helicopter.weight_capacity;
        
        int preferredMealType=69;
        int bestVillage = greedyFind(homeCity,h,problem,villageNeeds,distanceCap,remainingDistance,preferredMealType);
        if(bestVillage == -1) continue;
        
        int MealDemand = villageNeeds[bestVillage].first;
        int OtherDemand = villageNeeds[bestVillage].second;

        int carried_dry=0, carried_perish=0, carried_other=0;

        auto pickMeal = [&](double weight, int &Mtemp, int& take_temp){
            if (weight <= 0) return;
            int can = floor(weightCap/ weight);
            int carried = min(can, Mtemp);
            take_temp += carried;
            weightCap -= carried * weight;
            Mtemp -= carried;
        };

        if (preferredMealType==1) {
            pickMeal(weight_perish, MealDemand, carried_perish);
            pickMeal(weight_dry, MealDemand, carried_dry);
        } else {
            pickMeal(weight_dry, MealDemand, carried_dry);
            pickMeal(weight_perish, MealDemand, carried_perish);
        }
        if (weightCap > 0 && OtherDemand > 0) {
            int canCarry = (int)floor(weightCap / weight_other);
            int carried = min(canCarry, OtherDemand);
            carried_other += carried;
            weightCap -= carried * weight_other;
            OtherDemand -= carried;
        }
        
        if (carried_dry + carried_perish + carried_other == 0) {
            // Nothing to carry; avoid infinite loops. 
            //Mark village as done if already zero need.
            continue;
        }

        Trip trip;
        trip.dry_food_pickup        = (int)carried_dry;
        trip.perishable_food_pickup = (int)carried_perish;
        trip.other_supplies_pickup  = (int)carried_other;

        Drop drop;
        drop.village_id     = problem.villages[bestVillage].id; // keep the external id in the output
        drop.dry_food       = (int)carried_dry;
        drop.perishable_food= (int)carried_perish;
        drop.other_supplies = (int)carried_other;
        trip.drops.push_back(drop);

        helPlan.trips.push_back(trip);

        // update demands 
        villageNeeds[bestVillage].first -= (carried_dry+carried_perish);
        villageNeeds[bestVillage].first = max(0,villageNeeds[bestVillage].first);
        villageNeeds[bestVillage].second -= carried_other;
        villageNeeds[bestVillage].second = max(0,villageNeeds[bestVillage].second);

                                                                                                                
        solution.pb(helPlan);
    }
    return solution;
}



//ATTEMPTS TO SWAP THE FIRST DROPS OF TWO RANDOMLY CHOSEN TRIPS
static bool nbd_swap_two_trip_drops(Solution& sol, const ProblemData& p, std::mt19937& rng){
    vector<pair<int,int>> trips;
    for (int helicopterIndex = 0; helicopterIndex < (int)sol.size(); ++helicopterIndex){
        for (int tripIndex = 0; tripIndex < (int)sol[helicopterIndex].trips.size(); ++tripIndex){
            if (!sol[helicopterIndex].trips[tripIndex].drops.empty())
                trips.emplace_back(helicopterIndex, tripIndex);
        }
    }
    if ((int)trips.size() < 2) return false;

    std::uniform_int_distribution<int> U(0, (int)trips.size()-1);
    int a = U(rng), b = U(rng);
    if (a == b) return false;

    auto [helicopterIndex1, tripIndex1] = trips[a];
    auto [helicopterIndex2, tripIndex2] = trips[b];

    int dropIndex1 = 0, dropIndex2 = 0;


    //SAVING THIS FOR LATER
    Drop d1 = sol[helicopterIndex1].trips[tripIndex1].drops[dropIndex1];
    Drop d2 = sol[helicopterIndex2].trips[tripIndex2].drops[dropIndex2];

    sol[helicopterIndex1].trips[tripIndex1].drops[dropIndex1] = d2;
    sol[helicopterIndex2].trips[tripIndex2].drops[dropIndex2] = d1;
    syncPickups(sol[helicopterIndex1].trips[tripIndex1]);
    syncPickups(sol[helicopterIndex2].trips[tripIndex2]);

    if (!planFeasible(p, sol[helicopterIndex1]) || !planFeasible(p, sol[helicopterIndex2])){
        // revert
        sol[helicopterIndex1].trips[tripIndex1].drops[dropIndex1] = d1;
        sol[helicopterIndex2].trips[tripIndex2].drops[dropIndex2] = d2;
        syncPickups(sol[helicopterIndex1].trips[tripIndex1]);
        syncPickups(sol[helicopterIndex2].trips[tripIndex2]);
        return false;
    }
    return true;
}

 // RELOCATES ONE DROP BETWEEN TWO TRIPS OF THE SAME HELICOPTER 
static bool nbd_relocate_drop_within_heli(Solution& sol, const ProblemData& p, std::mt19937& rng){
    // pick a helicopter with at least 2 non-empty trips
    vector<int> candidates;
    candidates.reserve(sol.size());
    for (int helicopterIndex = 0; helicopterIndex < (int)sol.size(); ++helicopterIndex){
        int nz = 0;
        for (const auto& t : sol[helicopterIndex].trips) if (!t.drops.empty()) ++nz;
        if (nz >= 2) candidates.push_back(helicopterIndex);
    }
    if (candidates.empty()) return false;

    std::uniform_int_distribution<int> Uh(0, (int)candidates.size() - 1);
    int helicopterIndex = candidates[Uh(rng)];

    HelicopterPlan plan = sol[helicopterIndex];

    vector<int> T;
    T.reserve(plan.trips.size());
    for (int tripIndex = 0; tripIndex < (int)plan.trips.size(); ++tripIndex)
        if (!plan.trips[tripIndex].drops.empty()) T.push_back(tripIndex);

    if ((int)T.size() < 2) return false;

    std::uniform_int_distribution<int> Ut(0, (int)T.size() - 1);
    int srcTi = T[Ut(rng)];
    int dstTi = T[Ut(rng)];
    if (srcTi == dstTi) return false;

    Trip& src = plan.trips[srcTi];
    Trip& dst = plan.trips[dstTi];

    // choose a drop from the source trip
    std::uniform_int_distribution<int> Ud(0, (int)src.drops.size() - 1);
    int dropIndex = Ud(rng);
    Drop moved = src.drops[dropIndex];

    // remove from source
    src.drops.erase(src.drops.begin() + dropIndex);
    syncPickups(src);

    const int heli_idx = heliIdxById(plan.helicopter_id);

    // best-position insertion by resulting trip distance, under feasibility
    int bestPos = -1;
    double bestDist = std::numeric_limits<double>::infinity();

    for (int pos = 0; pos <= (int)dst.drops.size(); ++pos){
        Trip candDst = dst;
        candDst.drops.insert(candDst.drops.begin() + pos, moved);
        syncPickups(candDst);

        if (!tripFeasible(p, heli_idx, candDst)) continue;

        HelicopterPlan tmpPlan = plan;
        tmpPlan.trips[dstTi] = candDst;
        if (!planFeasible(p, tmpPlan)) continue;

        double d = tripDistanceFor(p, heli_idx, candDst);
        if (d < bestDist){
            bestDist = d;
            bestPos = pos;
        }
    }

    if (bestPos < 0){
        // give up; no feasible insertion
        return false;
    }

    // commit insertion
    dst.drops.insert(dst.drops.begin() + bestPos, moved);
    syncPickups(dst);

    // if source trip became empty, remove it to save fixed cost in evaluation
    if (plan.trips[srcTi].drops.empty()){
        plan.trips.erase(plan.trips.begin() + srcTi);
    }

    if (!planFeasible(p, plan)) return false;

    // write back
    sol[helicopterIndex] = std::move(plan);
    return true;
}

// Neighborhood dispatcher
static bool apply_random_neighborhood(Solution& trialPlan, const ProblemData& p, std::mt19937& rng){
    std::uniform_int_distribution<int> U(0, 1);
    int pick = U(rng);

    if (pick == 0){
        if (nbd_relocate_drop_within_heli(trialPlan, p, rng)) return true;
        return nbd_swap_two_trip_drops(trialPlan, p, rng);
    } else {
        if (nbd_swap_two_trip_drops(trialPlan, p, rng)) return true;
        return nbd_relocate_drop_within_heli(trialPlan, p, rng);
    }
}

static Solution local_search_improve(const ProblemData& problem, const Solution& start, steady_clock::duration timePassed,
                                    int iters = 1000000000, uint32_t seed = 1337){
    std::mt19937 rng(seed);
    Solution cur = start;
    double curScore = evaluateSolution(problem, cur);

    Solution best = cur;
    double bestScore = curScore;

    auto allowed_duration = milliseconds(long(problem.time_limit_minutes * 60 * 1000));
    auto buffer = milliseconds(100); // 100ms safety margin
    auto remaining = allowed_duration - timePassed - buffer;
    auto deadline = steady_clock::now() + remaining;
    
    for (int it = 0; it < iters && steady_clock::now() < deadline; ++it){
        Solution trialPlan = cur;
        bool changed = apply_random_neighborhood(trialPlan, problem, rng);
        if (!changed) continue;

        if (!solutionFeasible(problem, trialPlan)) continue;
        double s = evaluateSolution(problem, trialPlan);
        if (s > curScore){
            cur = std::move(trialPlan);
            curScore = s;
            if (s > bestScore){
                best = cur;
                bestScore = s;
            }
        }
        if (steady_clock::now() >= deadline) break;
    }
    return best;
}

Solution solve(const ProblemData& problem) {
    cout << "Starting solver..." << endl;

    auto start_time = steady_clock::now();
 
    FillIndices(problem);
    Solution sol = generate_initial_solution(problem);
    repairSolution(problem, sol);                

    auto timePassed = steady_clock::now() - start_time;
    sol = local_search_improve(problem,sol,timePassed); //passing the time that has been spent in the fetching the initial solution and evalutating its score
    
    repairSolution(problem,sol);
    cout << "Solver finished." << endl;
    return sol;
}
