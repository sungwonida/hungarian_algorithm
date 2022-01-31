// AUTHOR: David Jung
// EMAIL: sungwonida@gmail.com

#include <vector>
#include <iostream>
#include <limits>
#include <string>
#include <algorithm>
#include <string.h> // memcpy
#include <cassert>

//#define DEBUG


using std::cout;

namespace david {
namespace algorithms {
namespace hungarian {
struct State {
    int n;
    int m;
    int *row;
    int *col;
    int n_row;
    int n_col;

    State(int _n, int _m) : n(_n), m(_m), n_row(0), n_col(0) {
        row = new int[n];
        col = new int[m];
        for (int i = n; i >=0; --i) row[i] = 0;
        for (int i = m; i >=0; --i) col[i] = 0;
    }

    State(State&& rhs) : n(rhs.n), m(rhs.m), n_row(rhs.n_row), n_col(rhs.n_col) {
        row = new int[n];
        col = new int[m];
        memcpy(&row[0], &rhs.row[0], n * sizeof(int));
        memcpy(&col[0], &rhs.col[0], m * sizeof(int));

        delete [] rhs.row;
        delete [] rhs.col;
        rhs.row = nullptr;
        rhs.col = nullptr;
    }

    ~State() {
        if (row) delete [] row;
        if (col) delete [] col;
    }

    State& operator=(State&& rhs) {
        n = rhs.n;
        m = rhs.m;
        n_row = rhs.n_row;
        n_col = rhs.n_col;

        row = new int[n];
        col = new int[m];
        memcpy(&row[0], &rhs.row[0], n * sizeof(int));
        memcpy(&col[0], &rhs.col[0], m * sizeof(int));

        delete [] rhs.row;
        delete [] rhs.col;
        rhs.row = nullptr;
        rhs.col = nullptr;

        return *this;
    }
};

#ifdef DEBUG
void print_mat(int N, int M, const float* mat) {
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < M; ++j)
            cout << mat[i * M + j] << " ";
        cout << "\n";
    }
}

void print_covered(const int N, const int M, const State& covered) {
    cout << "\nCovered state\n";
    for (int i = 0; i < N; ++i) {
        if (covered.row[i]) {
            for (int j = 0; j < M; ++j)
                cout << "1 ";
            cout << "\n";
        } else {
            for (int j = 0; j < M; ++j) {
                if (covered.col[j])
                    cout << "1 ";
                else
                    cout << "0 ";
            }
            cout << "\n";
        }
    }
}
#endif // DEBUG

float* clone_mat(int N, int M, const float* mat) {
    int len = N * M - 1;
    float* clone = new float[len];

    for (int i = len; i >= 0; --i)
        clone[i] = mat[i];

    return clone;
}

void free_mat(float* mat) {
    delete [] mat;
}

// Test if there's enough number of matching
static inline bool is_solved(int n, const State& covered) {
    return (covered.n_row + covered.n_col) >= n;
}

State cover(const int N, const int M, const float* working_cost, const State& n_zeros_of) {
    State covered(N, M);

    // Cover the rows and cols
    for (int i = N-1; i >= 0; --i) {
        for (int j = M-1; j >= 0; --j) {
            int idx = i * M + j;

            int nzr = n_zeros_of.row[i];
            int nzc = n_zeros_of.col[j];
            // cout << i << ", " << j << "]: "
            //           << nzr << ", " << nzc << ", "
            //           << working_cost[idx];

            if (working_cost[idx] == 0 &&
                covered.row[i] == 0 && covered.col[j] == 0) {

                int nzr = n_zeros_of.row[i];
                int nzc = n_zeros_of.col[j];

                if (nzc > nzr) {
                    covered.col[j] = 1;
                    covered.n_col += 1;
                    // cout << " C";
                } else {
                    covered.row[i] = 1;
                    covered.n_row += 1;
                    // cout << " R";
                }
            }
            // cout << "\n";
        }
    }

    return covered;
}

template<typename T>
bool compare_asc(T a, T b) { return a < b; }

template<typename T>
bool compare_des(T a, T b) { return a > b; }

void sort_by_zeros(int* buf, int n_buf, const int* n_zeros, const int mode) {
    if (mode == 0) {
        std::sort(buf, buf + n_buf,
                  [n_zeros] (int a, int b) {return n_zeros[a] < n_zeros[b];});
    } else {
        std::sort(buf, buf + n_buf,
                  [n_zeros] (int a, int b) {return n_zeros[a] > n_zeros[b];});
    }
}

void sort_by_cost(int* buf, int n_buf, const float* cost, const int idx, const int m, const int mode) {
    if (mode == 0) {
        std::sort(buf, buf + n_buf,
                  [cost, idx, m] (int a, int b) {return cost[idx + a*m] < cost[idx + b*m];});
    } else {
        std::sort(buf, buf + n_buf,
                  [cost, idx, m] (int a, int b) {return cost[idx + a*m] > cost[idx + b*m];});
    }
}

bool is_assignable(const int target, const std::vector<std::vector<int>> target_buf, const int i, const int n_queries, const int* queries, int* target_assigned) {

    int query = queries[i];

    if (i == n_queries - 1) {
        const std::vector<int>& buf = target_buf[query];

        for (auto& target : buf) {
            if (target_assigned[target] == -1) {
                return true;
            }
        }

        return false;
    }

    target_assigned[target] = query;

    int next_query = queries[i+1];
    const std::vector<int>& next_buf = target_buf[next_query];

    for (auto& next_target : next_buf) {
        if (target_assigned[next_target] != -1)
            continue;

        if (is_assignable(next_target, target_buf, i+1, n_queries, queries, target_assigned))
            return true;

        target_assigned[next_target] = -1;
    }

    return false;
}

float assign(const float* cost, const int N, const int M, const int mode, const float* working_cost, const State& n_zeros_of, int* assignment_index) {

    float total_cost = .0;

    // The target could be either workers or jobs.
    // If N <= M then target becomes jobs, otherwise, workers.
    int n_targets;
    int n_queries;
    int* n_zeros; // n_zeros_of_query

    if (N <= M) {
        n_targets = M;
        n_queries = N;
        n_zeros = n_zeros_of.row;
    } else {
        n_targets = N;
        n_queries = M;
        n_zeros = n_zeros_of.col;
    }

    int target_assigned[n_targets];
    memset(&target_assigned[0], -1, n_targets * sizeof(int));

    int queries[n_queries];
    for (int i = 0; i < n_queries; ++i)
        queries[i] = i;

    bool (*update_assignment)(float a, float b) = mode == 0 ? compare_asc<float> : compare_des<float>;


    std::vector<std::vector<int>> target_buf;

    if (N <= M) {
        for (int i = 0; i < n_queries; ++i) {
            std::vector<int> buf;

            for (int j = 0; j < n_targets; ++j) {
                int idx = i * M + j;
                if (working_cost[idx] == 0)
                    buf.emplace_back(j);
            }

            sort_by_cost(&buf[0], buf.size(), cost, i * M, 1, mode);
            target_buf.emplace_back(buf);
        }
    } else {
        for (int i = 0; i < n_queries; ++i) {
            std::vector<int> buf;

            for (int j = 0; j < n_targets; ++j) {
                int idx = j * M + i;
                if (working_cost[idx] == 0)
                    buf.emplace_back(j);
            }

            sort_by_cost(&buf[0], buf.size(), cost, i, M, mode);
            target_buf.emplace_back(buf);
        }
    }

#ifdef DEBUG
    cout << "sorted target_buf (" << std::string(N <= M ? "job" : "worker") << "):\n";
    for (auto& buf : target_buf) {
        for (int i = 0; i < buf.size(); ++i)
            cout << buf[i] << " ";
        cout << "\n";
    }
#endif

    // Decide who goes first
    // One that has the lower number of zeros than others should have more priority
    // Then, others are going to choose among the rest

#ifdef DEBUG
    cout << "queries (" << std::string(N <= M ? "workers" : "jobs") << "): ";
    for (int i = 0; i < n_queries; ++i)
        cout << queries[i] << " ";
    cout << "\n";

    cout << "n_zeros: ";
    for (int i = 0; i < n_queries; ++i)
        cout << n_zeros[i] << " ";
    cout << "\n";
#endif

    sort_by_zeros(queries, n_queries, n_zeros, 0);

#ifdef DEBUG
    cout << "sorted queries (" << std::string(N <= M ? "workers" : "jobs") << "): ";
    for (int i = 0; i < n_queries; ++i)
        cout << queries[i] << " ";
    cout << "\n";
#endif

    for (int i = 0; i < n_queries; ++i) {
        int query = queries[i];
        const std::vector<int>& buf = target_buf[query];

#ifdef DEBUG
        cout << "query (" << std::string(N <= M ? "worker" : "job") << "): " << query << "\n";
        cout << "target_assigned: ";
        for (int i = 0; i < n_targets; ++i)
            cout << target_assigned[i] << " ";
        cout << "\n";
#endif

        // Is assignable?
        int target = -1;

        for (auto& cand : buf) {
            if (target_assigned[cand] != -1)
                continue;

            int tmp_assigned[n_targets];
            memcpy(&tmp_assigned[0], &target_assigned[0], n_targets * sizeof(int));

            if (is_assignable(cand, target_buf, i, n_queries, queries, tmp_assigned)) {
#ifdef DEBUG
                cout << "found. target " << cand << " is assianable\n";
#endif
                target = cand;
                break;
            }
        }
        // There should be at least one matching
        assert(target != -1);

        int idx = N <= M ? query * M + target : target * M + query;

        if (target_assigned[target] == -1) {
            // Initial assignment for the target
            assignment_index[query] = target;
            target_assigned[target] = query;
            total_cost += cost[idx];
        } else {
            // Find for the better cost if any
            int prev_query = target_assigned[target];
            float prev_cost = cost[prev_query * M + target];
            float curr_cost = cost[idx];

            if (update_assignment(curr_cost, prev_cost)) {
                assignment_index[prev_query] = -1; // Cancel the assignment
                assignment_index[query] = target;
                total_cost = total_cost - prev_cost + curr_cost;
            }
        }
    }

    // In case of assigning workers to each job (reverse order)
    // convert the assignment to right order
    if (N > M) {
        int tmp[N];
        memset(&tmp[0], -1, N * sizeof(int));

        for (int i = 0; i < N; ++i)
            tmp[assignment_index[i]] = i;

        memcpy(&assignment_index[0], &tmp[0], N * sizeof(int));
    }

    return total_cost;
}

float find_lowest(const int idx, const int N, const int M, const float* cost, const int axis) {
    float min = std::numeric_limits<float>::max();

    if (axis == 0) {
        // Find the value in the row
        for (int j = M-1; j >= 0; --j) {
            float v = cost[idx * M + j];
            if (v < min) min = v;
        }
    } else {
        // Find the value in the column
        for (int i = N-1; i >= 0; --i) {
            float v = cost[i * M + idx];
            if (v < min) min = v;
        }
    }

    return min;
}

float find_highest(const int idx, const int N, const int M, const float* cost, const int axis) {
    float max = std::numeric_limits<float>::lowest();

    if (axis == 0) {
        // Find the value in the row
        for (int j = M-1; j >= 0; --j) {
            float v = cost[idx * M + j];
            if (v > max) max = v;
        }
    } else {
        // Find the value in the column
        for (int i = N-1; i >= 0; --i) {
            float v = cost[i * M + idx];
            if (v > max) max = v;
        }
    }

    return max;
}


float find_lowest_uncovered(const int N, const int M, const float* working_cost, const State& covered) {
    // Find the smallest uncovered value
    float min = std::numeric_limits<float>::max();
    bool found = false;

    for (int i = N-1; i >= 0; --i) {
        if (!covered.row[i]) {
            for (int j = M-1; j >= 0; --j) {
                if (!covered.col[j]) {
                    float v = working_cost[i * M + j];
                    if (v < min) {
                        min = v;
                        found = true;
                    }
                }
            }
        }
    }

    if (!found) min = 0;

    return min;
}

float find_highest_uncovered(const int N, const int M, const float* working_cost, const State& covered) {
    // Find the biggest uncovered value
    float max = std::numeric_limits<float>::lowest();
    bool found = false;

    for (int i = N-1; i >= 0; --i) {
        if (!covered.row[i]) {
            for (int j = M-1; j >= 0; --j) {
                if (!covered.col[j]) {
                    float v = working_cost[i * M + j];
                    if (v > max) {
                        max = v;
                        found = true;
                    }
                }
            }
        }
    }

    if (!found) max = 0;

    return max;
}


float solve(const float* cost, const int N, const int M, const int mode, int* assignment_index) {
    bool solved = false;

#ifdef DEBUG
    cout << "\nGiven cost\n";
    print_mat(N, M, cost);
#endif

    // clone the original
    // the clone should be released after use
    float* working_cost = clone_mat(N, M, cost);

    State covered(N, M);
    State n_zeros_of(N, M);

    float (*find_criteria)(const int, const int, const int, const float*, const int);
    float (*find_criteria_uncovered)(const int, const int, const float*, const State&);

    if (mode == 0) {
        find_criteria = find_lowest;
        find_criteria_uncovered = find_lowest_uncovered;
    } else {
        find_criteria = find_highest;
        find_criteria_uncovered = find_highest_uncovered;
    }

    // STEP 1.
    // Subtract the lowest/highest value in each row from every element in the row
    for (int i = N-1; i >= 0; --i) {

        float v = find_criteria(i, N, M, working_cost, 0);

        // Subtract the lowest/highest value from every element in the row
        for (int j = M-1; j >= 0; --j) {
            int idx = i * M + j;
            working_cost[idx] -= v;
            if (working_cost[idx] == 0) {
                n_zeros_of.row[i] += 1;
                n_zeros_of.col[j] += 1;
            }
        }
    }

#ifdef DEBUG
    cout << "\nFinished step 1\n";
    print_mat(N, M, working_cost);
#endif

    // STEP 2.
    // If a column doesn't contain a zero
    // subtract the lowest/highest value from every element in the column
    for (int j = M-1; j >= 0; --j) {
        if (n_zeros_of.col[j] == 0) {
            float v = find_criteria(j, N, M, working_cost, 1);

            // Subtract the lowest/highest value from every element in the column
            for (int i = N-1; i >= 0; --i) {
                int idx = i * M + j;
                working_cost[idx] -= v;
                if (working_cost[idx] == 0) {
                    n_zeros_of.row[i] += 1;
                    n_zeros_of.col[j] += 1;
                }
            }
        }
    }

#ifdef DEBUG
    cout << "\nFinished step 2\n";
    print_mat(N, M, working_cost);
#endif

    covered = cover(N, M, working_cost, n_zeros_of);
#ifdef DEBUG
    print_covered(N, M, covered);
#endif

    // STEP 3.
    // Add the smallest uncovered value to elements that are covered by 2 lines
    // and subtract it from all uncovered elements
    // Repeat until solved

    while (!solved) {
        float v = find_criteria_uncovered(N, M, working_cost, covered);

        if (v != 0) {
#ifdef DEBUG
            cout << "The " << std::string(mode == 0 ? "smallest" : "biggest") << " uncovered value is " << v << "\n";
#endif

            for (int i = N-1; i >= 0; --i) {
                if (!covered.row[i]) {
                    for (int j = M-1; j >= 0; --j) {
                        if (!covered.col[j]) {
                            int idx = i * M + j;
                            working_cost[idx] -= v;
                            if (working_cost[idx] == 0) {
                                n_zeros_of.row[i] += 1;
                                n_zeros_of.col[j] += 1;
                            }
                        }
                    }
                }
            }

#ifdef DEBUG
            cout << "Subtracted the " << std::string(mode == 0 ? "smallest" : "biggest") << " uncovered value from all uncovered value\n";
            print_mat(N, M, working_cost);
#endif

            for (int i = N-1; i >= 0; --i) {
                if (covered.row[i]) {
                    for (int j = M-1; j >= 0; --j) {
                        if (covered.col[j]) {
                            // covered by 2 lines
                            int idx = i * M + j;
                            float prev = working_cost[idx];
                            working_cost[idx] += v;

                            if (working_cost[idx] == 0) {
                                n_zeros_of.row[i] += 1;
                                n_zeros_of.col[j] += 1;
                            } else if (prev == 0) {
                                n_zeros_of.row[i] -= 1;
                                n_zeros_of.col[j] -= 1;
                            }
                        }
                    }
                }
            }

#ifdef DEBUG
            cout << "Added the " << std::string(mode == 0 ? "smallest" : "biggest") << " uncovered value to elements that are covered by 2 lines\n";
            print_mat(N, M, working_cost);
#endif

            covered = cover(N, M, working_cost, n_zeros_of);
#ifdef DEBUG
            print_covered(N, M, covered);
#endif
        }

        solved = is_solved(N < M ? N : M, covered);
#ifdef DEBUG
        cout << "\nSolved? " << std::string((solved ? "Yes!" : "No (" + std::to_string(covered.n_row + covered.n_col) + ")")) << "\n";
#endif
    }

    float total_cost = assign(cost, N, M, mode, working_cost, n_zeros_of, assignment_index);
    free_mat(working_cost);

    return total_cost;
}
} // hungarian
} // algorithms
} // david

class TestCase {
    const float* cost_map;
    const int n;
    const int m;
    const int mode;
    const int gt_cost;
    const std::vector<int> gt_indices;
    int computed_cost;
    std::vector<int> computed_indices;

public:
    TestCase(
        const float* _cost_map,
        int _n,
        int _m,
        int _mode,
        int _gt_cost,
        std::vector<int> _gt_indices)
        : cost_map(_cost_map),
          n(_n),
          m(_m),
          mode(_mode),
          gt_cost(_gt_cost),
          gt_indices(_gt_indices),
          computed_indices(_n, -1) {
        }

    bool run() {
        computed_cost = david::algorithms::hungarian::solve(cost_map, n, m, mode, &computed_indices[0]);
        if (computed_cost == gt_cost && computed_indices == gt_indices)
            return true;
        return false;
    }

    void show_failed_reason() {
        cout << "========================================\n";
        cout << "Expected:\n" << "\tcost: " << gt_cost << "\n\tindices: ";
        for (auto& idx : gt_indices) cout << idx << " ";
        cout << "\nGot:\n" << "\tcost: " << computed_cost << "\n\tindices: ";
        for (auto& idx : computed_indices) cout << idx << " ";
        cout << "\n========================================\n";
    }
};

void run_tests() {
    // TEST CASES
    float cost1[3][4] = {{3, 7, 5, 11},
                        {5, 4, 6, 3},
                        {6, 10, 1, 1}};

    float cost2[3][2] = {{10, 6},
                        {10, 6},
                        {4, 2}};

    float cost3[3][3] = {{5, 9, 1},
                        {10, 3, 2},
                        {8, 7, 4}};

    float cost4[3][3] = {{2, 3, 3},
                         {3, 2, 3},
                         {3, 3, 2}};

	float cost5[4][4] = {{82,83,69,92},
                        {77,37,49,92},
                        {11,69,5,86},
                        {8,9,98,23}};

    float cost6[4][4] = {{3, 4, 5, 6},
                        {7, 3, 4, 7},
                        {6, 5, 6, 3},
                        {2, 8, 5, 7}};

    std::vector<TestCase> tests;
    // TestCase: cost_map, n, m, mode, gt_cost, gt_indices
    tests.emplace_back(TestCase(&cost1[0][0], 3, 4, 0, 7, {0, 3, 2}));
	tests.emplace_back(TestCase(&cost1[0][0], 3, 4, 1, 27, {3, 2, 1}));
    tests.emplace_back(TestCase(&cost2[0][0], 3, 2, 0, 10, {1, -1, 0}));
    tests.emplace_back(TestCase(&cost3[0][0], 3, 3, 0, 12, {2, 1, 0}));
    tests.emplace_back(TestCase(&cost4[0][0], 3, 3, 0, 6, {0, 1, 2}));
    tests.emplace_back(TestCase(&cost5[0][0], 4, 4, 0, 140, {2, 1, 0, 3}));
    tests.emplace_back(TestCase(&cost6[0][0], 4, 4, 0, 13, {2, 1, 3, 0}));

    int i = 0;
    int n_passed = 0;
    for (auto& test : tests) {
        cout << i++ << ": ";
        if (test.run()) {
            cout << "PASSED\n";
            n_passed += 1;
        } else {
            cout << "FAILED\n";
            test.show_failed_reason();
        }
    }
    if (n_passed == tests.size())
        cout << "ALL PASSED\n";
}

int main() {
    run_tests();
    return 0;
}
