int elem_priority (int x) {
    {
        return x;
    }
}
typedef int elem;
int elem_priority (elem e);
typedef struct heap_header* pq;
pq pq_new (int capacity);
bool pq_empty (pq P);
bool pq_full (pq P);
void pq_insert (pq P, elem e);
elem pq_min (pq P);
elem pq_delmin (pq P);
typedef struct heap_header {int limit;
                            int next;
                            elem[] data;} struct heap_header;
typedef struct heap_header* heap;
int priority (struct heap_header* H, int i) {
    {
        return elem_priority((*(H)).data[i]);
    }
}
bool is_heap (struct heap_header* H) {
    {
        if ((!(H != NULL))) {
            {
                return false;
            }
        }
        else {
            {
            }
        }
        if ((!((1 <= (*(H)).next) ? ((*(H)).next <= (*(H)).limit) : false))) {
            {
                return false;
            }
        }
        else {
            {
            }
        }
        int #0;
        {
            #0 = 2;
            int i;
            {
                i = #0;
                while ((i < (*(H)).next)) {
                    {
                        {
                            if ((!(priority(H, (i / 2)) <= priority(H, i)))) {
                                {
                                    return false;
                                }
                            }
                            else {
                                {
                                }
                            }
                            i = (i + 1);
                        }
                    }
                }
            }
        }
        return true;
    }
}
bool is_heap_except_up (heap H, int n) {
    {
        if ((H == NULL)) {
            {
                return false;
            }
        }
        else {
            {
            }
        }
        if ((!((1 <= (*(H)).next) ? ((*(H)).next <= (*(H)).limit) : false))) {
            {
                return false;
            }
        }
        else {
            {
            }
        }
        int #1;
        {
            #1 = 2;
            int i;
            {
                i = #1;
                while ((i < (*(H)).next)) {
                    {
                        {
                            if (((i != n) ? (!(priority(H, (i / 2)) <= priority(H, i))) : false)) {
                                {
                                    return false;
                                }
                            }
                            else {
                                {
                                }
                            }
                            if (((((i / 2) == n) ? (((i / 2) / 2) >= 1) : false) ? (!(priority(H, ((i / 2) / 2)) <= priority(H, i))) : false)) {
                                {
                                    return false;
                                }
                            }
                            else {
                                {
                                }
                            }
                            i = (i + 1);
                        }
                    }
                }
            }
        }
        return true;
    }
}
bool is_heap_except_down (heap H, int n) {
    {
        if ((H == NULL)) {
            {
                return false;
            }
        }
        else {
            {
            }
        }
        if ((!((1 <= (*(H)).next) ? ((*(H)).next <= (*(H)).limit) : false))) {
            {
                return false;
            }
        }
        else {
            {
            }
        }
        int #2;
        {
            #2 = 2;
            int i;
            {
                i = #2;
                while ((i < (*(H)).next)) {
                    {
                        {
                            if ((((i / 2) != n) ? (!(priority(H, (i / 2)) <= priority(H, i))) : false)) {
                                {
                                    return false;
                                }
                            }
                            else {
                                {
                                }
                            }
                            if (((((i / 2) == n) ? (((i / 2) / 2) >= 1) : false) ? (!(priority(H, ((i / 2) / 2)) <= priority(H, i))) : false)) {
                                {
                                    return false;
                                }
                            }
                            else {
                                {
                                }
                            }
                            i = (i + 1);
                        }
                    }
                }
            }
        }
        return true;
    }
}
bool pq_empty (heap H) {
    {
        return ((*(H)).next == 1);
    }
}
bool pq_full (heap H) {
    {
        return ((*(H)).next == (*(H)).limit);
    }
}
heap pq_new (int capacity) {
    heap #3;
    {
        #3 = alloc(struct heap_header);
        heap H;
        {
            H = #3;
            (*(H)).limit = (capacity + 1);
            (*(H)).next = 1;
            (*(H)).data = alloc_array(elem, (capacity + 1));
            return H;
        }
    }
}
void swap (elem[] A, int i, int j) {
    elem #4;
    {
        #4 = A[i];
        elem tmp;
        {
            tmp = #4;
            A[i] = A[j];
            A[j] = tmp;
        }
    }
}
void pq_insert (heap H, elem e) {
    {
        (*(H)).data[(*(H)).next] = e;
        (*(H)).next = ((*(H)).next + 1);
        int #5;
        {
            #5 = ((*(H)).next - 1);
            int i;
            {
                i = #5;
                while (((i > 1) ? (priority(H, i) < priority(H, (i / 2))) : false)) {
                    {
                        {
                            swap((*(H)).data, i, (i / 2));
                            i = (i / 2);
                        }
                    }
                }
                return ;
            }
        }
    }
}
void sift_down (heap H, int i) {
    int #6;
    {
        #6 = (*(H)).next;
        int n;
        {
            n = #6;
            int #7;
            {
                #7 = (2 * i);
                int left;
                {
                    left = #7;
                    int #8;
                    {
                        #8 = (left + 1);
                        int right;
                        {
                            right = #8;
                            while ((left < n)) {
                                {
                                    {
                                        if (((priority(H, i) <= priority(H, left)) ? ((right >= n) ? true : (priority(H, i) <= priority(H, right))) : false)) {
                                            {
                                                return ;
                                            }
                                        }
                                        else {
                                            {
                                            }
                                        }
                                        if (((right >= n) ? true : (priority(H, left) < priority(H, right)))) {
                                            {
                                                {
                                                    swap((*(H)).data, i, left);
                                                    i = left;
                                                }
                                            }
                                        }
                                        else {
                                            {
                                                {
                                                    swap((*(H)).data, i, right);
                                                    i = right;
                                                }
                                            }
                                        }
                                        left = (2 * i);
                                        right = (left + 1);
                                    }
                                }
                            }
                            return ;
                        }
                    }
                }
            }
        }
    }
}
elem pq_delmin (heap H) {
    int #9;
    {
        #9 = (*(H)).next;
        int n;
        {
            n = #9;
            elem #10;
            {
                #10 = (*(H)).data[1];
                elem min;
                {
                    min = #10;
                    (*(H)).data[1] = (*(H)).data[(n - 1)];
                    (*(H)).next = (n - 1);
                    if (((*(H)).next > 1)) {
                        {
                            sift_down(H, 1);
                        }
                    }
                    else {
                        {
                        }
                    }
                    return min;
                }
            }
        }
    }
}
elem pq_min (heap H) {
    {
        return (*(H)).data[1];
    }
}
typedef struct rand {int seed;} struct rand;
typedef struct rand* rand_t;
rand_t init_rand (int seed) {
    rand_t #11;
    {
        #11 = alloc(struct rand);
        rand_t gen;
        {
            gen = #11;
            (*(gen)).seed = seed;
            return gen;
        }
    }
}
int rand (rand_t gen) {
    {
        (*(gen)).seed = (((*(gen)).seed * 1664525) + 1013904223);
        return (*(gen)).seed;
    }
}
bool is_sorted (int[] A, int lower, int upper) {
    {
        int #12;
        {
            #12 = lower;
            int i;
            {
                i = #12;
                while ((i < (upper - 1))) {
                    {
                        {
                            if ((!(A[i] <= A[(i + 1)]))) {
                                {
                                    return false;
                                }
                            }
                            else {
                                {
                                }
                            }
                            i = (i + 1);
                        }
                    }
                }
            }
        }
        return true;
    }
}
int* init (int param) {
    {
        return alloc(int);
    }
}
void prepare (int* data, int param) {
    {
        *(data) = 0;
    }
}
void run (int* data, int param) {
    int #13;
    {
        #13 = 5;
        int num_tests;
        {
            num_tests = #13;
            int #14;
            {
                #14 = param;
                int n;
                {
                    n = #14;
                    rand_t #15;
                    {
                        #15 = init_rand(2343432205);
                        rand_t gen;
                        {
                            gen = #15;
                            int[] #16;
                            {
                                #16 = alloc_array(int, n);
                                int[] A;
                                {
                                    A = #16;
                                    int #17;
                                    {
                                        #17 = 0;
                                        int j;
                                        {
                                            j = #17;
                                            while ((j < num_tests)) {
                                                {
                                                    {
                                                        pq #18;
                                                        {
                                                            #18 = pq_new(n);
                                                            pq P;
                                                            {
                                                                P = #18;
                                                                int #19;
                                                                {
                                                                    #19 = 0;
                                                                    int i;
                                                                    {
                                                                        i = #19;
                                                                        while ((i < n)) {
                                                                            {
                                                                                {
                                                                                    assert((!pq_full(P)));
                                                                                    pq_insert(P, rand(gen));
                                                                                    assert((!pq_empty(P)));
                                                                                    i = (i + 1);
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                                assert(pq_full(P));
                                                                int #20;
                                                                {
                                                                    #20 = 0;
                                                                    int i;
                                                                    {
                                                                        i = #20;
                                                                        while ((i < n)) {
                                                                            {
                                                                                {
                                                                                    assert((!pq_empty(P)));
                                                                                    A[i] = pq_delmin(P);
                                                                                    assert((!pq_full(P)));
                                                                                    i = (i + 1);
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                                assert(is_sorted(A, 0, n));
                                                                assert((!pq_full(P)));
                                                                assert(pq_empty(P));
                                                            }
                                                        }
                                                        j = (j + 1);
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    *(data) = A[(n - 1)];
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
int checksum (int* data, int param) {
    {
        return *(data);
    }
}
int main () {
    int* #21;
    {
        #21 = init(1000);
        int* data;
        {
            data = #21;
            prepare(data, 1000);
            run(data, 1000);
            return *(data);
        }
    }
}