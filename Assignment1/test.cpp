#include "io_handler.h"
#include "structures.h"
#include <iostream>

#include <unordered_map>
#include <random>
#include <algorithm>
#include <limits>

using namespace std;

int main(int argc, char* argv[]) {
    if (argc != 3) {
        cerr << "Usage: " << argv[0] << " <input_filename> <output_filename>" << endl;
        return 1;
    }

    string input_filename = argv[1];
    string output_filename = argv[2];

    try {
        ProblemData problem = readInputData(input_filename);
        for (int i = 0; i < (int)problem.helicopters.size(); ++i) {
            cerr << "Heli id=" << problem.helicopters[i].id
                << " home_city_id=" << problem.helicopters[i].home_city_id
                << " cities.size=" << problem.cities.size() << "\n";
        }
        for (int i = 0; i < (int)problem.villages.size(); ++i) {
            cerr << "Village ext id=" << problem.villages[i].id
                << " (index " << i << ") coords=("
                << problem.villages[i].coords.x << "," << problem.villages[i].coords.y << ")\n";
        }
    }
    catch (const runtime_error& e) {
        cerr << "An error occurred: " << e.what() << endl;
        return 1;
    }
    
}
