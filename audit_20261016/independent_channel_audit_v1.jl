#!/usr/bin/env julia
# A separate implementation: construct H(b)|environment vacuum> in the
# doubled CAR algebra. No inclusion or reuse of either original script.
# This is internal independent implementation, not external peer review.
using LinearAlgebra, SparseArrays, Random, Printf, Test
BLAS.set_num_threads(1)
const SEED = 2026101607
const Rat = Rational{BigInt}
const CRat = Complex{Rat}
const SUMMARY = Dict{String,Float64}()

pairindices(d) = [(i,j) for j in 2:d for i in 1:j-1]
function car(n, ::Type{T}) where T
    N=2^n
    [begin
        rows=Int[]; cols=Int[]; vals=T[]
        for col in 0:N-1
            iszero(col & (1<<(mode-1))) && continue
            push!(rows, (col ⊻ (1<<(mode-1)))+1); push!(cols,col+1)
            push!(vals, isodd(count_ones(col & ((1<<(mode-1))-1))) ? -one(T) : one(T))
        end
        sparse(rows,cols,vals,N,N)
    end for mode in 1:n]
end
wedge(u,v) = [u[i]*v[j]-u[j]*v[i] for (i,j) in pairindices(length(u))]
function wedge_map(A)
    [A[i,k]*A[j,l]-A[i,l]*A[j,k] for (i,j) in pairindices(size(A,1)),
                                              (k,l) in pairindices(size(A,2))]
end
function pair_ann(c,p)
    sum(conj(p[t])*(c[j]*c[i]) for (t,(i,j)) in enumerate(pairindices(length(c))))
end
function make_frame(parts,weights)
    P=hcat([sum(lam*wedge(u,v) for (lam,u,v) in terms) for terms in parts]...)
    (; parts, weights, P)
end
function schur_constant(fr)
    function kernel(a,b)
        sum(abs(lx)*abs(ly)*(abs(dot(u,x))+abs(dot(u,y))+abs(dot(v,x))+abs(dot(v,y)))
            for (lx,u,v) in a for (ly,x,y) in b)
    end
    maximum(sum(fr.weights[y]*kernel(fr.parts[x],fr.parts[y]) for y in eachindex(fr.parts))
            for x in eachindex(fr.parts))
end

# J embeds the system Fock basis with all environmental modes empty.
# In the doubled basis, system modes have lower bit positions.
function direct_channel(fr,M,E)
    d=size(M,1); T=promote_type(eltype(fr.P),eltype(M),eltype(E)); D=2^d
    c=car(d,T); f=car(2d,T)
    b=[sum(conj(M[k,j])*f[k]+conj(E[k,j])*f[d+k] for k in 1:d) for j in 1:d]
    J=sparse(1:D,1:D,ones(T,D),D^2,D)
    output=spzeros(T,D^2,D)
    for x in axes(fr.P,2)
        B=pair_ann(b,fr.P[:,x]); output += fr.weights[x]*(B'*(B*J))
    end
    Henv=Matrix(output[1:D,:])
    N=Matrix{T}[]
    blocks=Vector{Matrix{T}}[]
    for k in 1:2
        envs=[e for e in 0:D-1 if count_ones(e)==k]
        bb=[Matrix(output[e*D+1:(e+1)*D,:]) for e in envs]
        push!(blocks,bb); push!(N,sum(B'B for B in bb))
    end
    beyond=[r+1 for r in 0:D^2-1 if count_ones(r>>d)>2]
    leakage=isempty(beyond) ? zero(real(one(T))) : maximum(abs,output[beyond,:];init=zero(real(one(T))))
    # A distinct construction of the filtered system Hamiltonian uses minors.
    PM=wedge_map(M)*fr.P
    BM=[Matrix(pair_ann(c,PM[:,x])) for x in axes(PM,2)]
    H=sum(fr.weights[x]*(BM[x]'BM[x]) for x in eachindex(BM))
    H0=sum(fr.weights[x]*Matrix(pair_ann(c,fr.P[:,x])'pair_ann(c,fr.P[:,x])) for x in eachindex(BM))
    # Third computation of environmental blocks: expand creation legs only.
    creations=[Matrix(sum(M[k,j]*c[k]' for k in 1:d)) for j in 1:d]
    parity=Diagonal(T[isodd(count_ones(i)) ? -1 : 1 for i in 0:D-1])
    X1=[zeros(T,D,D) for _ in 1:d]
    X2=[zeros(T,D,D) for _ in pairindices(d)]
    PE=wedge_map(E)*fr.P
    for x in axes(fr.P,2), (a,(i,j)) in enumerate(pairindices(d))
        for e in 1:d
            X1[e] += fr.weights[x]*fr.P[a,x]*(E[e,j]*creations[i]-E[e,i]*creations[j])*BM[x]*parity
        end
    end
    for x in axes(fr.P,2), a in eachindex(X2)
        X2[a] += fr.weights[x]*PE[a,x]*BM[x]
    end
    # Numerical order of two-bit environments agrees with pairindices.
    (; H,H0,Henv,N1=N[1],N2=N[2],PhiH2=Matrix(output'output),blocks,X1,X2,leakage,BM)
end

function induced_fock(A)
    d=size(A,1); out=zeros(eltype(A),2^d,2^d)
    occupied=[[j for j in 1:d if !iszero(b & (1<<(j-1)))] for b in 0:2^d-1]
    for row in 1:2^d,col in 1:2^d
        length(occupied[row])==length(occupied[col]) || continue
        out[row,col]=isempty(occupied[row]) ? one(eltype(A)) : det(A[occupied[row],occupied[col]])
    end
    out
end

function exact_complex_case()
    d=3; I3=Matrix{CRat}(I,d,d)
    U=CRat[3//5 4im//5 0; 4im//5 3//5 0; 0 0 1]
    V=CRat[5//13 0 12im//13; 0 1 0; 12im//13 0 5//13]
    @test U'U==I3 && V'V==I3
    fr=make_frame([[(CRat(1),U[:,1],U[:,3])],[(CRat(1),U[:,2],U[:,3])]],Rat[1,2//3])
    M=V*Diagonal(CRat[3//5,5//13,15//17])*V'
    E=V*Diagonal(CRat[4//5,12//13,8//17])*V'
    @test M==M' && E==E' && M*M+E*E==I3
    r=direct_channel(fr,M,E)
    @test r.Henv==r.H
    @test r.PhiH2==r.H*r.H+r.N1+r.N2
    @test r.blocks[1]==r.X1 && r.blocks[2]==r.X2
    @test iszero(r.leakage)
    @test any(!iszero,imag.(M)) && any(!iszero,imag.(fr.P))
    println("EXACT_COMPLEX_RATIONAL: Phi(H)=HM; Phi(H^2)=HM^2+N1+N2; all signed blocks exact: PASS")
    println("EXACT_COMPLEX_RATIONAL_HM_2PARTICLE_DIAGONAL=",diag(r.H)[[4,6,7]])
end

randunitary(rng,d)=Matrix(qr(randn(rng,ComplexF64,d,d)).Q)
function complex_frame(rng,d; ranktwo=false,nonprojector=false)
    U=randunitary(rng,d)
    if ranktwo
        # Each label is a coherent superposition of two orthogonal Slater pairs.
        parts=[[(inv(sqrt(2.0)),U[:,1],U[:,2]),(im/sqrt(2.0),U[:,3],U[:,4])],
               [(0.6,U[:,1],U[:,3]),(0.8im,U[:,2],U[:,4])]]
        return make_frame(parts,nonprojector ? [2.7,0.4] : [1.0,1.0])
    else
        ps=pairindices(d)
        parts=[[(1.0,U[:,i],U[:,j])] for (i,j) in ps]
        weights=nonprojector ? [0.4+2.3x/length(ps) for x in eachindex(ps)] : ones(length(ps))
        return make_frame(parts,weights)
    end
end
function floating_case(label,fr,M,E;kernelcheck=true,relative=true)
    r=direct_channel(fr,M,E); d=size(M,1)
    beta=opnorm(fr.P*Diagonal(fr.weights)*fr.P'); C=schur_constant(fr)
    delta=opnorm(I-M*M); hnorm=max(1,opnorm(r.H)); tol=2e-10*hnorm^2
    residual=maximum([norm(r.Henv-r.H,Inf),norm(r.PhiH2-r.H*r.H-r.N1-r.N2,Inf),
        maximum(norm(a-b,Inf) for (a,b) in zip(r.blocks[1],r.X1)),
        maximum(norm(a-b,Inf) for (a,b) in zip(r.blocks[2],r.X2)),r.leakage])
    @test residual<tol
    l1=eigmin(Hermitian(C*delta*r.H-r.N1)); l2=eigmin(Hermitian(beta*delta^2*r.H-r.N2))
    @test l1>=-tol
    @test l2>=-tol
    @test eigmin(Hermitian(r.PhiH2-r.H*r.H))>=-tol
    F=eigen(Hermitian(r.H)); pos=findall(>(1e-10*hnorm),F.values)
    rel1=NaN;rel2=NaN
    if relative
        W=F.vectors[:,pos]*Diagonal(1 ./sqrt.(F.values[pos]))
        rel1=eigmax(Hermitian(W'*r.N1*W));rel2=eigmax(Hermitian(W'*r.N2*W))
        @test rel1 <= C*delta+1e-8
        @test rel2 <= beta*delta^2+1e-8
    end
    F0=eigen(Hermitian(r.H0)); zer0=findall(<(1e-10),F0.values)
    if kernelcheck
        K=induced_fock(inv(M))*F0.vectors[:,zer0]
        K=Matrix(qr(K).Q)[:,1:size(K,2)]
        @test norm(r.H*K,Inf)<tol
        @test length(zer0)==count(<(1e-10*hnorm),F.values)
    end
    gamma0=minimum(filter(>(1e-10),F0.values)); eta=C*delta+beta*delta^2
    @test eigmin(Hermitian(r.H*r.H-(gamma0-eta)*r.H))>=-tol
    SUMMARY["max_identity_residual"]=max(get(SUMMARY,"max_identity_residual",0.0),residual)
    @printf("%s,d=%d,beta=%.7g,C=%.7g,delta=%.7g,relN1=%.7g,relN2=%.7g,eta=%.7g,residual=%.3e,minSlack1=%.3e,minSlack2=%.3e\n",
        label,d,beta,C,delta,rel1,rel2,eta,residual,l1,l2)
    r
end

function numerical_sweep()
    rng=MersenneTwister(SEED)
    for d in 2:6, nonprojector in (false,true), delta in (0.002,0.37,0.97)
        fr=complex_frame(rng,d;nonprojector)
        U=randunitary(rng,d); losses=collect(range(delta/5,delta;length=d))
        M=U*Diagonal(sqrt.(1 .-losses))*U';E=U*Diagonal(sqrt.(losses))*U'
        floating_case(nonprojector ? "complex_nonprojector" : "complex_projector",fr,M,E)
    end
    for d in 4:6, nonprojector in (false,true), delta in (0.003,0.6)
        fr=complex_frame(rng,d;ranktwo=true,nonprojector)
        U=randunitary(rng,d); losses=collect(range(delta/5,delta;length=d))
        M=U*Diagonal(sqrt.(1 .-losses))*U';E=U*Diagonal(sqrt.(losses))*U'
        floating_case(nonprojector ? "slater_rank2_nonprojector" : "slater_rank2_projector",fr,M,E)
    end
    d=4;fr=complex_frame(rng,d);U=randunitary(rng,d)
    singularvalues=[1e-6,0.5,0.8,0.999999]
    M=U*Diagonal(singularvalues)*U';E=U*Diagonal(sqrt.(1 .-singularvalues.^2))*U'
    r=floating_case("near_singular",fr,M,E;kernelcheck=false,relative=false)
    # Exact mathematical kernel here is vacuum + all one-particle states,
    # since h2=I and M is invertible. A fixed absolute eigenvalue threshold
    # used by the old scripts can mislabel positive states as zero modes.
    numerical_nullity=count(<(1e-9),eigvals(Hermitian(r.H)))
    @test numerical_nullity>d+1
    println("THRESHOLD_DIAGNOSTIC: true kernel dimension=",d+1,"; threshold(1e-9) reports=",numerical_nullity,
            "; min(M)=1e-6; this is a threshold failure, not a kernel theorem counterexample")
end

function assumption_counterexamples()
    I2=Matrix{Rat}(I,2,2);fr=make_frame([[(Rat(1),I2[:,1],I2[:,2])]],Rat[3])
    M=(3//5)*I2;E=(4//5)*I2;r=direct_channel(fr,M,E);delta=Rat(16//25)
    @test r.N2[4,4] == 3*delta^2*r.H[4,4]
    @test r.N2[4,4] > delta^2*r.H[4,4]
    println("COUNTEREXAMPLE_OMIT_BETA: beta=3, N2/(delta^2 HM)=",r.N2[4,4]/(delta^2*r.H[4,4]),
            "; exact violation=",r.N2[4,4]-delta^2*r.H[4,4])
    M=diagm(Rat[0,1]);E=diagm(Rat[1,0]);r=direct_channel(fr,M,E)
    @test iszero(r.H) && !iszero(r.H0)
    println("COUNTEREXAMPLE_DROP_INVERTIBILITY: d=2, M=diag(0,1); dim ker H0=3; dim ker HM=4")
end

println("INDEPENDENT_CHANNEL_AUDIT Julia=",VERSION," seed=",SEED," BLAS_threads=",BLAS.get_num_threads())
println("Convention: c(v) is antilinear; system bits precede environment bits; no external SDP rerun.")
@testset "Independent doubled-CAR channel audit" begin
    exact_complex_case()
    numerical_sweep()
    assumption_counterexamples()
end
println("SUMMARY=",SUMMARY)
