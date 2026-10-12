# Checks the type recursion of the paper against Hardin's b-file for A246479.
# Usage: curl -sO https://oeis.org/A246479/b246479.txt && python3 check_bfile.py
b=[int(l.split()[1]) for l in open('b246479.txt') if l.strip() and not l.startswith('#')]
pos=[];d=1
while len(pos)<len(b):
    for n in range(1,d+1): pos.append((n,d+1-n))
    d+=1
def step(v,k):  # Sxm, Sym use (k-1-e) = (k-2) when e=1
    e=1 if k%2==0 else 0
    A,B,Bm,C,Cm,D,Dm,E,E1,E2,E3=v
    Sxx=A+e*Bm+(k-1-e)*B; Snm=C+D+e*E3+(k-3-e)*E; Sxm=Dm+(k-2)*E1; Sym=Cm+(k-2)*E2
    return (Sxx,Snm,Sym,Snm,Sxm,Sxx-B,Sxx-Bm,Snm-E,Snm-E3,Sxm-E1,Sym-E2)
def T(n,k):
    v=(1,)*11
    for _ in range(n-1): v=step(v,k)   # V_L for length L+3 = n+3 -> L=n
    v=step(v,k)
    e=1 if k%2==0 else 0
    A,B,Bm,C,Cm,D,Dm,E,E1,E2,E3=v
    Sxx=A+e*Bm+(k-1-e)*B; Snm=C+D+e*E3+(k-3-e)*E; Sxm=Dm+(k-2)*E1; Sym=Cm+(k-2)*E2
    return (k+1-e)*Sxx + e*k*Sxm + e*k*Sym + (k+1-e)*(k-1-e)*Snm
bad=[(n,k) for (n,k),x in zip(pos,b) if T(n,k)!=x]; print(len(b),bad[:20],len(bad))
