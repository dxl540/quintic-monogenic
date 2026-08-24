import sys
import traceback
import time

from sage.all import Primes
import random

pari.allocatemem(2^32, silent=True)
_ = pari.set_real_precision(5000)

R.<x> = PolynomialRing(QQ)
R2.<x1, x2> = PolynomialRing(QQ, 2)
RR = RealField(5000)
CC = ComplexField(5000)
S.<xR> = PolynomialRing(CC)

timing_file = None

def time_check(stage_name, time_list, indents=0):
    """A helper function for displaying time diagnostics.
    
    Parameters:
        stage_name: name of stage, as to be displayed
        time_list: list of timestamps of when previous stages finished
        indents: how many indents to print before the time diagnostics
                 (useful for nested functions)
    
    Output:
        Appends the current time to time_list, then prints the stage name,
        time that stage took, and total time elapsed (all in seconds).
    """
    current_time = time.time()
    start_time = time_list[0]
    last_time = time_list[-1]
    time_list.append(current_time)
    this_stage = current_time - last_time
    total_time = current_time - start_time
    print("\t" * indents + f"{stage_name:<56s}"+ f"{this_stage:12.3f}{total_time:12.3f}", file=timing_file)
    

def pari_polynomial_to_sage(p, K):
    """
    Convert a PARI polynomial in the defining generator into K.

    Parameters:
        p: polynomial in PARI
        K: number field in Sage
    
    Returns:
        the polynomial in the defining generator of K (as an element of K)
    """
    p = pari(p).lift()
    P = K.polynomial_ring()

    coeffs = [
        QQ(p.polcoef(i))
        for i in range(K.degree())
    ]

    return K(P(coeffs))

def pari_integral_basis_coordinates_to_sage(coords, nf, K):
    """
    Convert a PARI coordinate vector relative to an integral basis of nf into
    an element of the Sage number field K.
    
    Parameters:
        coords: coordinate vector
        nf: number field in PARI
        K: number field in Sage
    
    Returns:
        the element of K with the corresponding coordinate vector
    """
    elem = nf.nfbasistoalg(coords)
    return pari_polynomial_to_sage(elem, K)

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

def pp_elem_pari(nf, p, k, timing = False):
    """Determine all ideals in the number field L12 with norm p^k for prime p.
    Same as pp_elem, but in PARI instead for performance.

    Parameters:
        nf: number field in PARI
        p: prime number
        k: nonnegative integer
    
    Yields:
        All fractional ideals of nf with norm p^k (in PARI)
    
    Requires:
        p is prime
    """
    if timing:
        time_list = [time.time()]
        # print("\t" + f"enumerating ideals of norm {p}^{k}...")

    ideals = nf.idealprimedec(p)
    def helper(current, r, i):
        if i == len(ideals):
            if r == 0:
                yield current
        else:
            ideal = current
            n = ideals[i][3]
            for j in range(0, r // n + 1):
                yield from helper(ideal, r - j*n, i+1)
                ideal = nf.idealmul(ideal, ideals[i])
    yield from helper(nf.idealhnf(1), k, 0)

    if timing:
        time_check(f"enumerating ideals of norm {p}^{k}", time_list, 2)

def pp_elem_count(L12, p, k, timing = False):
    """Compute the number of ideals in the number field L12 with norm p^k for prime p.
    Same as pp_elem, but only returns count instead and is much quicker.

    Parameters:
        L12: number field
        p: prime number
        k: nonnegative integer
    
    Yields:
        Number of fractional ideals of L12 with norm p^k
    
    Requires:
        p is prime
    """
    ideals = L12.factor(p)
    ideal_norms = [log(ideal.norm(), p) for ideal, _ in ideals]
    seen = {}
    def helper(r, i):
        if (r, i) in seen:
            return seen[(r, i)]
        if i == len(ideals):
            return 1 if r == 0 else 0
        else:
            n = ideal_norms[i]
            out = 0
            for j in range(0, r // n + 1):
                out += helper(r - j*n, i+1)
            seen[(r, i)] = out
            return out
    return helper(k, 0)

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
    
    ideals_list = cartesian_product([list(pp_elem(L12, p, e*k, timing=timing)) for p, e in factors])
    
    if timing:
        time_check(f"enumerating all {len(ideals_list)} ideals of norm {I}^{k}", time_list, 1)

    for ideals in ideals_list:
        ideal = product(ideals)
        if ideal.is_principal():
            out.add(ideal.gens_reduced()[0])

    if timing:
        time_check(f"checking for principal ideals", time_list, 1)
    return out

def all_elem_pari(L12, I, k, timing = False):
    """Determine all elements (up to associates) in L12 which generate
    a power basis of index |I^k|.
    Same as all_elem, but in PARI instead for performance.

    WARNING: outputs may not be certified.

    Parameters:
        L12: number field in Sage
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
        
    nf = pari(L12)
    bnf = nf.bnfinit()
    
    if timing:
        time_check("factoring ideal I", time_list, 1)
        print("\t" + f"enumerating ideals of norm {I}^{k}...")
    
    ideals_list = cartesian_product([list(pp_elem_pari(nf, p, e*k, timing=timing)) for p, e in factors])
    
    if timing:
        time_check(f"enumerating all {len(ideals_list)} ideals of norm {I}^{k}", time_list, 1)

    for ideals in ideals_list:
        ideal = nf.idealhnf(1)
        for ideal_factor in ideals:
            ideal = nf.idealmul(ideal, ideal_factor)
        result = bnf.bnfisprincipal(ideal)
        if all(c == 0 for c in result[0]):
            coords = result[1]
            if len(coords) == 0:
                raise Exception("PARI failed to return a generator of principal ideal. Try increasing PARI's precision?")
            
            gamma = pari_integral_basis_coordinates_to_sage(result[1], nf, L12)
            if abs(gamma.norm()) != abs(I^k):
                raise Exception(f"PARI returned a generator of norm {gamma.norm()} instead of target norm {I}^{k}")
            out.add(gamma)

    if timing:
        time_check(f"checking for principal ideals", time_list, 1)
    return out

def all_elem_count(L12, I, k, timing = False):
    """Determine the number of ideals of L12 with norm |I^k|.
    Meant to be a quick way to estimate size of output of all_elem.

    Parameters:
        L12: number field
        I: nonzero integer
        k: nonnegative integer

    Yields:
        Number of ideals of L12 of norm |I^k|
    """
    if I == 1 or I == -1:
        return 1
    out = 1
    factors = factor(I)
    for p, e in factors:
        out *= pp_elem_count(L12, p, e*k, timing=timing)
    return out

def reduce_gammas(L, L12, coeff_bound = 3, max_index = 10^4, timing = False):
    """Helper function to find a more favorable presentations for all_generators.
    Specifically, looks for an element of L whose index I minimizes the quantity
    all_elem_count(L12, I, k), so that the number of gammas to be enumerated incomplete
    all_generators is smaller.

    Parameters:
        L: degree-5 number field
        L12: degree-10 number field, should have principal generator
             the sum of any two distinct roots of l
        coeff_bound: bound on coefficients (searches by coefficients on integral basis)
        max_index: bound on index I (elements with index > I are automatically skipped)

    Returns:
        an element of L with hopefully reduced number of gammas
    """
    basis = L.integral_basis()
    L_disc = L.discriminant()
    def ind(new_z):
        return sqrt(L.discriminant([1, new_z, new_z^2, new_z^3, new_z^4]) / L_disc)

    best_z = L.absolute_generator()
    best_index = ind(best_z)
    best_gammas = all_elem_count(L12, ind(best_z), 9)
    if best_gammas == 1:
        return best_z
    seen = {best_index: best_gammas}

    for coeffs in cartesian_product([range(-coeff_bound, coeff_bound+1)] * 5):
        new_z = sum(c * b for c, b in zip(basis, coeffs))
        if new_z.minpoly().degree() == 5:
            new_index = ind(new_z)
            if new_index < max_index:
                if new_index not in seen:
                    new_gammas = all_elem_count(L12, new_index, 9)
                    seen[new_index] = new_gammas
                    if new_gammas < best_gammas or (new_gammas == best_gammas and new_index < best_index):
                        if new_gammas == 1:
                            return new_z
                        best_z = new_z
                        best_index = new_index
                        best_gammas = new_gammas

    return best_z

def all_generators(poly, certify, reduce_poly, verbose = False, timing = False):
    """Determine whether the quintic field defined by the polynomial is monogenic.

    Currently only works on totally-real quintic fields with Galois group S5.

    Parameters:
        poly: quintic polynomial
        certify: whether to ensure PARI-side computations are certified.
                 if true, may cause stalling.
                 if false, enumeration may be incomplete due to finite-index
                 discrepancies in computing unit group.
        reduce_poly: whether to attempt to find an alternative presentation of
                     NumberField(poly) to speed up enumeration.
                     performance may be improved when true.
        verbose: flag for additional details.
                 if true, additional details will be printed (e.g., intermediate bounds)
        timing: flag for timing diagnostics.
                if true, timing details will be printed for each step.

    Returns:
        set of elements of NumberField(poly) which generate a power basis

    Requires:
        poly has degree 5
        poly is monic
        poly is irreducible
        poly has Galois group S5
    """
    if timing:
        time_list = [time.time()]

    # ensure reproducibility
    random.seed(int(42))
    set_random_seed(42)

    old_L.<z> = NumberField(poly)
    if reduce_poly:
        # reduction process -- compute L and L12 as below, then reduce
        ppoly = poly(x=x1)
        ppoly2 = ppoly.resultant(ppoly(x1=x2-x1), x1)
        poly2 = sqrt(ppoly2 / (32 * poly(x=x2/2)))(x2=x).squarefree_part()
        old_L12.<old_z12> = NumberField(poly2)
        new_z = reduce_gammas(old_L, old_L12, timing=timing)
        f = new_z.minpoly()
        if timing:
            time_check(f"reduced: {f}", time_list)
    else:
        f = poly
        new_z = z

    assert f.degree() == 5, f"{f} is not degree 5"
    assert f.is_irreducible(), f"{f} is not irreducible"
    
    generators = set()
    
    L.<z_used> = NumberField(f)
    phi = L.hom([new_z], old_L)
    assert L.galois_group().order() == 120, f"{f} does not have Galois group S5"
    
    # get starting index and target index (discriminant)
    L_disc = L.discriminant()
    OL = L.ring_of_integers()
    I0 = sqrt(L.discriminant([1, z_used, z_used^2, z_used^3, z_used^4]) / L_disc)

    # determine real roots
    g = f(xR)
    xis = [r[0] for r in g.roots()]
    assert len(xis) == 5, f"{f} is not totally real"

    # define number field L12, the degree-10 number field spanned by
    # r+s and rs for two roots r and s of f
    ff = f(x=x1)
    ff2 = ff.resultant(ff(x1=x2-x1), x1)
    f2 = sqrt(ff2 / (32 * f(x=x2/2)))(x2=x).squarefree_part()
    if f2.leading_coefficient() < 0:
        f2 = -f2
    
    L12.<z12> = NumberField(f2)
    basis12 = L12.integral_basis()

    if timing:
        time_check("L, L12, real roots, and embeddings", time_list)

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

    # get fundamental units
    if certify:
        es = UnitGroup(L12).fundamental_units()
    else:
        bnf = pari(f2).bnfinit()
        pari_units = bnf.bnf_get_fu()
        es = [pari_polynomial_to_sage(u, L12) for u in pari_units]

        OL12 = L12.ring_of_integers()
        for e in es:
            if e not in OL12:
                raise Exception("PARI returned non-integral element as fundamental unit")
            if abs(e.norm()) != 1:
                raise Exception("PARI returned non-unit as fundamental unit")

    matrix12 = Matrix(QQ, 10, 10, [b.list() for b in basis12])
    ematrix12 = Matrix(QQ, 9, 10, [eps.list() for eps in es])
    eint = ematrix12 * (matrix12 ^ -1)

    bad_denominators = set()
    for e in es:
        for p, _ in factor(e.denominator()):
            bad_denominators.add(p)

    if timing:
        time_check("computing L12 unit group", time_list)
    
    # get all gamma of norm I0^9
    if certify:
        gammas = all_elem(L12, I0, 9, timing=timing)
    else:
        gammas = all_elem_pari(L12, I0, 9, timing=timing)
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
            if tp > 1000 and p not in bad_denominators and gamma_denom%tp != 0 and len(f.roots(GF(tp))) == 5:
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
            generator = sum(y_vector[i] * z_used^(i+1) for i in range(4)) / I0
            
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
            _ = pari.set_real_precision(max(53, floor(2*log(H, 2))))
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
                
                solutions = pari.qfminim(perturbed_matrix, q+t, -1, 2)
                solution_vectors = solutions[2].sage().columns()
        
                for b in solution_vectors:
                    test(b)
                    
        if timing:
            time_check("enumeration during reduction of H", gamma_time_list, 1)
        
        # final enumeration
        last_H = h_list[-1]
        if verbose:
            print(f"enumerating final bound H={last_H}")
        pari.set_real_precision(max(53, floor(2*log(last_H, 2))))
        a_vector = vector([logalphas[i][j][k] for i, j, k, in I_triples])
        v_matrix = Matrix(CC, q, 9, [logvs[i][j][k] for i, j, k in I_triples])
        augmented_matrix = v_matrix.augment(a_vector)
        form_matrix = augmented_matrix.T * augmented_matrix
        perturbed_matrix = form_matrix + perturbation
        
        solutions = pari.qfminim(perturbed_matrix, (q*(log(last_H))^2)+t, -1, 2)
        solution_vectors = solutions[2].sage().columns()
        
        for b in solution_vectors:
            test(b)

        if timing:
            time_check("final enumeration", gamma_time_list, 1)
            time_check(f"enumerating {len(generators) - old_count} generators for gamma {gamma_index+1} of {num_gammas}", time_list)

    return set([phi(generator) for generator in generators])

f = R(sys.argv[1])
job_number = int(sys.argv[2])

log_file_name = f"logs/{job_number}.log"
result_file_name = f"results/{job_number}.out"

with open(log_file_name, "w") as log_file:
    with open(result_file_name, "w") as result_file:
        timing_file = log_file
        print("real 1000-input run 3 (no certify)", file=result_file)
        print(f, file=result_file)
        print("", file=result_file)
        try:
            gens = all_generators(f, certify=false, reduce_poly=true, timing=True)
            for zz in gens:
                print(zz, "\t\t", zz.charpoly(), file=result_file)
            if not gens:
                print("no generators", file=result_file)
        except Exception:
            print("error occurred", file=result_file)
            traceback.print_exc()
            sys.exit(1)