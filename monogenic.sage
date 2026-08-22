import sys
import traceback
import time

from sage.all import Primes
import random

pari.allocatemem(2^32)

R.<x> = PolynomialRing(QQ)
R2.<x1, x2> = PolynomialRing(QQ, 2)
S.<xR> = PolynomialRing(CC)
RR = RealField(5000)
CC = ComplexField(5000)

def time_check(stage_name, time_list, indents=0):
    """A helper function for displaying time diagnostics."""
    current_time = time.time()
    start_time = time_list[0]
    last_time = time_list[-1]
    time_list.append(current_time)
    this_stage = current_time - last_time
    total_time = current_time - start_time
    # print("\t" * indents + stage_name + f" took {this_stage:.3f} seconds, total {total_time:.3f}")
    print('        ' * indents + f"{stage_name:<56s}"+ f"{this_stage:12.3f}{total_time:12.3f}")

def pp_elem(L12, p, k, timing = False):
    """Determine all ideals in the number field L12 with norm p^k for prime p.

    Parameters:
        L12: number field
        p: prime number
        k: nonnegative integer
    
    Yields:
        All fractional ideals of L12 with norm p^k
    
    Requires:
        p is prime
    """
    if timing:
        time_list = [time.time()]
        # print("\t" + f"enumerating ideals of norm {p}^{k}...")

    ideals = L12.factor(p)
    ideal_norms = [(ideal, log(ideal.norm(), p)) for ideal, _ in ideals]
    def helper(current, r, i):
        if i == len(ideals):
            if r == 0:
                yield current
        else:
            ideal = current
            n = ideal_norms[i][1]
            for j in range(0, r // n + 1):
                yield from helper(ideal, r - j*n, i+1)
                ideal *= ideal_norms[i][0]
    yield from helper(L12.ideal([1]), k, 0)

    if timing:
        time_check(f"enumerating ideals of norm {p}^{k}", time_list, 2)

def all_elem(L12, I, k, timing = False):
    """Determine all elements (up to associates) in L12 which generate
    a power basis of index |I^k|.

    WARNING: uses .gens_reduced(), which can sometimes stall.

    Parameters:
        L12: number field
        I: nonzero integer
        k: nonnegative integer

    Yields:
        All elements of L12 with index +-I^k, up to associates
    """
    if timing:
        time_list = [time.time()]
        print("finding all values of gamma...")

    if I == 1 or I == -1:
        if timing:
            print("\t" + "|I| = 1, this step is trivial")
        return [L12(1)]
    out = set()
    factors = factor(I)
    
    if timing:
        time_check("factoring ideal I", time_list, 1)
        print("\t" + f"enumerating ideals of norm {I}^{k}...")
    
    ideals_list = cartesian_product([list(pp_elem(L12, p, e*k, timing)) for p, e in factors])
    
    if timing:
        time_check(f"enumerating all {len(ideals_list)} ideals of norm {I}^{k}", time_list, 1)

    for ideals in ideals_list:
        ideal = product(ideals)
        if ideal.is_principal():
            out.add(ideal.gens_reduced()[0])
    if timing:
        time_check(f"checking for principal ideals", time_list, 1)
    return out

def all_generators(f, verbose = False, timing = False):
    """Determine whether the quintic field defined by the polynomial is monogenic.

    Currently only works on totally-real quintic fields with Galois group S5.

    Parameters:
        f: quintic polynomial

    Returns:
        set of elements of NumberField(f) which generate a power basis

    Requires:
        f has degree 5
        f is monic
        f is irreducible
        f has Galois group S5
    """
    if timing:
        time_list = [time.time()]

    # ensure reproducibility
    random.seed(int(42))
    set_random_seed(42)

    assert f.degree() == 5, f"{f} is not degree 5"
    assert f.is_irreducible(), f"{f} is not irreducible"
    
    generators = set()
    
    L.<z> = NumberField(f)
    assert L.galois_group().order() == 120, f"{f} does not have Galois group S5"
    
    # get starting index and target index (discriminant)
    L_disc = L.discriminant()
    OL = L.ring_of_integers()
    I0 = sqrt(L.discriminant([1, z, z^2, z^3, z^4]) / L_disc)

    # determine real roots
    g = f(xR)
    xis = [r[0] for r in g.roots()]
    assert len(xis) == 5, f"{f} is not totally real"

    # define number field L12, the degree-10 number field spanned by
    # r+s and rs for two roots r and s of f
    ff = f(x=x1)
    ff2 = ff.resultant(ff(x1=x2-x1), x1)
    f2 = sqrt(ff2 / (32 * f(x=x2/2)))(x2=x).squarefree_part()
    
    L12.<z12> = NumberField(f2)
    basis12 = L12.integral_basis()

    # get fundamental units
    es = UnitGroup(L12).fundamental_units()
    matrix12 = Matrix(QQ, 10, 10, [b.list() for b in basis12])
    ematrix12 = Matrix(QQ, 9, 10, [eps.list() for eps in es])
    eint = ematrix12 * (matrix12 ^ -1)

    # get embeddings of L12, and match them up with pairs of real roots
    Lijs = [[0 for _ in range(5)] for _ in range(5)]
    for i in range(5):
        for j in range(5):
            if i != j:
                target = xis[i] + xis[j]
                for K in L12.embeddings(CC):
                    if abs(K(z12) - target) <= 10^-15:
                        Lijs[i][j] = K
                        break
                else:
                    raise Exception("No suitable embedding found")

    if timing:
        time_check("initialization, units, and embeddings", time_list)
    
    # get all gamma of norm I0^9
    gammas = all_elem(L12, I0, 9, timing)
    num_gammas = len(gammas)
    if verbose:
        print(f"found {num_gammas} possible values of gamma")
    if timing:
        time_check(f"finding all {num_gammas} values of gamma", time_list)

    for gamma_index, gamma in enumerate(gammas):
        if verbose:
            print(f"trying gamma {gamma_index+1} of {num_gammas}")
        if timing:
            print(f"trying gamma {gamma_index+1} of {num_gammas}...")
            gamma_time_list = [time.time()]

        # compute all real values of alpha, e, v and their logs
        alphas = [[[0 for _ in range(5)] for _ in range(5)] for _ in range(5)]
        logalphas = [[[0 for _ in range(5)] for _ in range(5)] for _ in range(5)]
        e_values = [[[0 for _ in range(9)] for _ in range(5)] for _ in range(5)]
        vs = [[[[0 for _ in range(9)] for _ in range(5)] for _ in range(5)] for _ in range(5)]
        logvs = [[[[0 for _ in range(9)] for _ in range(5)] for _ in range(5)] for _ in range(5)]
        
        for i in range(5):
            for j in range(5):
                if i != j:
                    for r in range(9):
                        e_values[i][j][r] = Lijs[i][j](es[r])
        
        for i in range(5):
            for j in range(5):
                for k in range(5):
                    if i != j != k != i:
                        alphas[i][j][k] = (Lijs[i][j](gamma) * (xis[i] - xis[j])) / (Lijs[i][k](gamma) * (xis[i] - xis[k]))
                        logalphas[i][j][k] = log(abs(alphas[i][j][k]))
                        for r in range(9):
                            vs[i][j][k][r] = e_values[i][j][r] / e_values[i][k][r]
                            logvs[i][j][k][r] = log(abs(vs[i][j][k][r]))
        
        if timing:
            time_check("computing alphas, es, vs, and logs", gamma_time_list, 1)

        def row_norm(M):
            out = 0
            for row in M:
                out = max(out, sum(abs(r) for r in row))
            return out
        
        all_triples = [(i,j,k) for k in range(5) for j in range(5) for i in range(5) if i != j != k != i]
        
        # sample random sets of triples to find one which is good for bounding
        used_triples = None
        M = None
        best_c = infinity
        for _ in range(1000):
            sample = random.sample(all_triples, 9)
            sample_M = Matrix(CC, 9, 9, [logvs[i][j][k] for i, j, k in sample])
            if sample_M.det() < 10^-50:
                # probably linearly dependent
                continue
            sample_c = row_norm(sample_M ^ -1)
            if sample_c < best_c:
                used_triples = sample
                M = sample_M
                best_c = sample_c
        
        if timing:
            time_check("sampling triples for Baker-type bound", gamma_time_list, 1)

        # Baker-type bound (currently relies on Galois group S5)
        c1 = best_c
        c2 = max(map(abs, flatten(logalphas)))
        C0 = 18 * factorial(11) * (10^11) * ((32*120)^12) * log(2*10*120)
        
        alpha_height = (sum(map(lambda l: max(0, l), flatten(logalphas))) / 60)
        C0 *= max(alpha_height, c2/120, 1/120)
        flat_logvs = flatten(logvs, max_level = 2)
        for r in range(9):
            v_height = (sum(map(lambda l: max(0, l[r]), flat_logvs)) / 60)
            v_max = max(map(lambda l: abs(l[r]), flat_logvs))
            C0 *= max(v_height, v_max/120, 1/120)
        
        B0 = 10^10
        while log(2*c2) - B0/c1 >= -C0 * log(B0):
            B0 *= 10
        B0 = max(B0, -c1 * log(0.398 / c2))
        
        c3 = 2 * c2
        c4 = 1 / c1
        
        if timing:
            time_check("computing Baker-type bound B0", gamma_time_list, 1)
        
        # LLL reduction for reduction of bound B
        worst_B = 0
        for (i0, j0, k0) in [(0, 1, 2), (0, 2, 1)]:
            B = B0
            B_exp = 10
            
            while B_exp < 20:
                C = B ^ B_exp
                lattice = identity_matrix(CC, 9).augment(C * vector([logvs[i0][j0][k0][r] for r in range(9)]))
                int_lattice = lattice.apply_map(lambda l: ZZ(round(RR(l))))
                lll = int_lattice.LLL()
                a1 = lll.row(0).norm()
                new_B = floor((log(C) + log(c3) - log(B)) / c4) + 1
                if a1 >= sqrt(11*2^9) * B and new_B < B:
                    B = new_B
                else:
                    B_exp += 1
        
            worst_B = max(worst_B, B)
        if verbose:
            print(f"using reduced bound B = {worst_B}")
        if timing:
            time_check(f"computing reduced bound B = {worst_B}", gamma_time_list, 1)
        
        sorted_triples = [(i, j, k) for i in range(5) for j in range(i+1, 5) for k in range(j+1, 5)]
        
        # sample triples for bound reduction of H
        def generate_I(length):
            sample = random.sample(sorted_triples, length)
            out = []
            for i, j, k in sample:
                if random.randint(0, 1) == 0:
                    out.append((i, j, k))
                else:
                    out.append((i, k, j))
                if random.randint(0, 1) == 0:
                    out.append((j, k, i))
                else:
                    out.append((j, i, k))
                if random.randint(0, 1) == 0:
                    out.append((k, i, j))
                else:
                    out.append((k, j, i))
            return random.sample(out, len(out))
        
        target_length = 5
        attempts = 0
        I_triples = generate_I(target_length)
        I_matrix = Matrix(CC, 9, 9, [logvs[i][j][k] for i, j, k in I_triples[:9]])
        while I_matrix.det() < 10^-50:
            attempts += 1
            if attempts%200 == 0:
                target_length += 1
            I_triples = generate_I(target_length)
            I_matrix = Matrix(CC, 9, 9, [logvs[i][j][k] for i, j, k in I_triples[:9]])
        q = len(I_triples)

        if timing:
            time_check("sampling triples for reduction of bound H", gamma_time_list, 1)
        
        # set up quick sieve test modulo p
        # find p in which f splits completely
        p = None
        p_roots = None
        gamma_denom = gamma.denominator()
        for tp in Primes():
            if tp > 1000 and gamma_denom%tp != 0 and len(f.roots(GF(tp))) == 5:
                p = tp
                p_roots = [r[0] for r in f.roots(GF(tp))]
                break
                
        if timing:
            time_check(f"finding sieving prime p = {p}", gamma_time_list, 1)
        
        # compute all alpha, gamma, e, v modulo p -- uses Galois group S5
        p_alphas = [[[0 for _ in range(5)] for _ in range(5)] for _ in range(5)]
        p_gammas = [[0 for _ in range(5)] for _ in range(5)]
        p_es = [[[0 for _ in range(9)] for _ in range(5)] for _ in range(5)]
        p_vs = [[[[0 for _ in range(9)] for _ in range(5)] for _ in range(5)] for _ in range(5)]
        
        Fp = GF(p)
        gamma_coords = [Fp(coord) for coord in gamma.list()]
        for i in range(5):
            for j in range(5):
                if i != j:
                    p_zij = p_roots[i] + p_roots[j]
                    p_gammas[i][j] = sum(p_zij^k * g_coord for k, g_coord in enumerate(gamma_coords))
                    for r in range(9):
                        e_coords = [Fp(coord) for coord in es[r].list()]
                        p_es[i][j][r] = sum(p_zij^k * coord for k, coord in enumerate(e_coords))
        
        for i in range(5):
            for j in range(5):
                for k in range(5):
                    if i != j != k != i:
                        p_alphas[i][j][k] = (p_gammas[i][j] * (p_roots[i] - p_roots[j])) / (p_gammas[i][k] * (p_roots[i] - p_roots[k]))
                        for r in range(9):
                            p_vs[i][j][k][r] = p_es[i][j][r] / p_es[i][k][r]
        
        if timing:
            time_check("computing everything modulo p", gamma_time_list, 1)

        # sieve and test solutions
        old_count = len(generators)
        def test(b):
            if b[-1] == -1:
                b = -b
            if b[-1] != 1:
                return None
            b = b[:-1]
                
            first_term = p_alphas[0][1][2]
            second_term = p_alphas[2][1][0]
            for r in range(9):
                first_term *= p_vs[0][1][2][r] ^ b[r]
                second_term *= p_vs[2][1][0][r] ^ b[r]
            if first_term + second_term != 1:
                return None
                
            first_term = p_alphas[2][3][4]
            second_term = p_alphas[4][3][2]
            for r in range(9):
                first_term *= p_vs[2][3][4][r] ^ b[r]
                second_term *= p_vs[4][3][2][r] ^ b[r]
            if first_term + second_term != 1:
                return None
        
            system_matrix = Matrix(CC, 4, 4, [[xis[i]^j - xis[0]^j for j in range(1, 5)] for i in range(1, 5)])
            target_vector = vector(CC, 4, [(xis[0] - xis[i]) * Lijs[0][i](gamma) * product(e_values[0][i][r] ^ b[r] for r in range(9)) for i in range(1, 5)])
        
            y_vector = (system_matrix ^ -1 * target_vector).apply_map(lambda y: round(real(y)))
            generator = sum(y_vector[i] * z^(i+1) for i in range(4)) / I0
            
            if L.discriminant([generator^i for i in range(5)]) != L_disc:
                return None
            is_integer = False
            for res in range(I0):
                if generator + (res / I0) in OL:
                    is_integer = True
                    generator += res / I0
                    break
            if not is_integer:
                return None
            
            if generator not in generators:
                generators.add(generator)
            return None
        
        # enumerate and reduce bound H
        H0 = 10^100
        for i in range(5):
            for j in range(5):
                for k in range(5):
                    if i != j != k != i:
                        Hijk = abs(logalphas[i][j][k]) + worst_B * sum(abs(logvs[i][j][k][r]) for r in range(9))
                        H0 = max(H0, Hijk)
        h_list = [H0, 10^50, 10^20, 10^10, 10^8, 10^7, 10^6, 3*10^5, 10^5, 5*10^4, 2*10^4, 10^4, 5000, 2000, 1000, 500, 200, 100, 50, 20, 10]
        t = 1
        perturbation = diagonal_matrix([t] + [0] * 9)
        
        for H, h in zip(h_list, h_list[1:]):
            _ = gp.set_real_precision(max(53, floor(2*log(H, 2))))
            a_vector = vector([logalphas[i][j][k] for i, j, k, in I_triples])
            v_matrix = Matrix(CC, q, 9, [logvs[i][j][k] for i, j, k in I_triples])
            augmented_matrix = v_matrix.augment(a_vector)
            
            for s in range(q):
                test_vec = [1/log(H)] * q
                test_vec[s] = 1/log((h-1)/(h-2))
                scale_matrix = diagonal_matrix(test_vec)
                scaled_matrix = scale_matrix * augmented_matrix
                form_matrix = scaled_matrix.T * scaled_matrix
                if verbose:
                    print(f"trying bounds H={H} and h={h}, triple {s}")
                
                perturbed_matrix = form_matrix + perturbation
                
                solutions = gp.qfminim(perturbed_matrix, q+t, -1, 2)
                solution_vectors = solutions[3].sage().columns()
        
                for b in solution_vectors:
                    test(b)
                    
        if timing:
            time_check("enumeration during reduction of H", gamma_time_list, 1)
        
        # final enumeration
        last_H = h_list[-1]
        if verbose:
            print(f"enumerating final bound H={last_H}")
        gp.set_real_precision(max(53, floor(2*log(last_H, 2))))
        a_vector = vector([logalphas[i][j][k] for i, j, k, in I_triples])
        v_matrix = Matrix(CC, q, 9, [logvs[i][j][k] for i, j, k in I_triples])
        augmented_matrix = v_matrix.augment(a_vector)
        form_matrix = augmented_matrix.T * augmented_matrix
        perturbed_matrix = form_matrix + perturbation
        
        solutions = gp.qfminim(perturbed_matrix, (q*(log(last_H))^2)+t, -1, 2)
        solution_vectors = solutions[3].sage().columns()
        
        for b in solution_vectors:
            test(b)

        if timing:
            time_check("final enumeration", gamma_time_list, 1)
            time_check(f"enumerating {len(generators) - old_count} generators for gamma {gamma_index+1} of {num_gammas}", time_list)

    return generators

print("real 1000-input run 2")
f = R(sys.argv[1])
print(f)
print()
try:
    gens = all_generators(f)
    for zz in gens:
        print(zz, "\t\t", zz.charpoly())
    if not gens:
        print("no generators")
except Exception:
    print("error occurred")
    traceback.print_exc()