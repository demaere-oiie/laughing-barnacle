# work through p.47, def'n 4.4.1 and thm 4.4.2 of Vickers, *Topology via Logic*, via concrete examples

# -- Semilattice ---------------------------------------------------------------

# operations in the semilattice
def isect(x,y):
    return "".join(sorted(set(x)&set(y)))

def union(x,y):
    return "".join(sorted(set(x)|set(y)))

# some concrete downsets
# N5: pentagon lattice
n5 = set("""
0
0x
0xz
0y
0xy
0xyz
01xyz
""".split())

# M3: diamond lattice
m3 = set("""
0
0x
0y
0z
0xy
0xz
0yz
0xyz
01xyz
""".split())

def alpha(ds):
    return set(c for d in ds for c in d)

def le(x,y,ds):
    return all(x in d for d in ds if y in d)

# generate the principal downset of x
def lower(x,ds):
    return "".join(sorted(y for y in alpha(ds) if le(y,x,ds)))

# if d is a principal downset, return its representative
def rep(d,ds):
    for c in d:
        if all(le(y,c,ds) for y in d):
            return c
    return None

# check that a system of downsets is closed under intersection and union
def assert_closure(ds):
  for x in ds:
    for y in ds:
      assert(isect(x,y) in ds)
      assert(union(x,y) in ds)

# check that a system of downsets is distributive
def assert_distr(ds):
  for x in ds:
    for y in ds:
      for z in ds:
         a = isect(x,union(y,z))
         b = union(isect(x,y),isect(x,z))
         assert(a == b)

# check that lower and rep are inverses
def assert_reps(ds):
   for s in alpha(ds):
       assert(rep(lower(s,ds),ds)==s)
   for d in ds:
       if rep(d,ds): # ignore non-principal downsets
           assert(lower(rep(d,ds),ds)==d)

# -- Coverages -----------------------------------------------------------------

# cover c is compatible with downset d
def covers(c,d):
    u,a = c.split()
    return not isect(u,d)==u or isect(a,d)==a

# the c-ideals are the downsets in ds compatible with the coverage cs
def c_ideals(cs,ds):
    return set(d for d in ds if all(covers(c,d) for c in cs))

# generate a principal coverage
def coverage(c,ds):
    def meet(x,y,ds):
        a = set(lower(x,ds))
        b = set(lower(y,ds))
        return rep("".join(sorted(a&b)),ds)
    u,a = c.split()
    return sorted(set("".join(sorted(set(meet(t,s,ds) for t in u)))+" "+s
        for s in alpha(ds) if le(s,a,ds)))

# ------------------------------------------------------------------------------
if __name__=="__main__":
    # we should've ensured this by hand
    assert_closure(n5)
    assert_closure(m3)

    # the lattices are not distributive, but their downsets are
    assert_distr(n5)
    assert_distr(m3)

    # lower and rep should be inverse on principal downsets
    assert_reps(n5)
    assert_reps(m3)

    print(coverage("xy 1",n5))
    for d in c_ideals(coverage("xy 1",n5),n5):
        print(d)
    print("----")
    print(coverage("xy 1",m3))
    for d in c_ideals(coverage("xy 1",m3),m3):
        print(d)
