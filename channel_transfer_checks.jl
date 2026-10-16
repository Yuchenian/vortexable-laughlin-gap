#!/usr/bin/env julia
# Independent finite-Fock-space checks of the proposed loss-channel transfer lemma.
# Standard libraries only. No files are modified by this script.
using LinearAlgebra, Random, Printf, Test

function combinations(n::Int, k::Int)
    out = Vector{Vector{Int}}()
    function rec!(a, first)
        if length(a) == k
            push!(out, copy(a)); return
        end
        for j in first:(n-k+length(a)+1)
            push!(a, j); rec!(a, j+1); pop!(a)
        end
    end
    rec!(Int[], 1)
    out
end

function fermions(d::Int, ::Type{T}=Float64) where T
    out = [zeros(T, 1<<d, 1<<d) for _ in 1:d]
    for j in 1:d, b in 0:(1<<d)-1
        mask = 1 << (j-1)
        if b & mask != 0
            sg = isodd(count_ones(b & (mask-1))) ? -one(T) : one(T)
            out[j][(b ⊻ mask)+1,b+1] = sg
        end
    end
    out
end

function sphere_pairs(Q::Int)
    d=Q+1; ps=combinations(d,2); lookup=Dict(Tuple(p)=>i for (i,p) in enumerate(ps))
    L=zeros(length(ps),length(ps))
    for (a,p) in enumerate(ps), slot in 1:2
        i=p[slot]-1
        if i < Q
            q=copy(p); q[slot]+=1
            q[1]==q[2] && continue
            L[lookup[Tuple(q)],a] += sqrt((Q-i)*(i+1))
        end
    end
    r=2Q-1; V=zeros(length(ps),r); V[lookup[(1,2)],1]=1
    for n in 0:r-2
        V[:,n+2]=L*V[:,n+1]/sqrt((n+1)*(2(Q-1)-n))
    end
    @assert norm(V'V-I) < 1e-11
    ps,V
end

function annihilator_pairs(c, ps, V)
    [sum(conj(V[a,p])*(c[ps[a][2]]*c[ps[a][1]]) for a in eachindex(ps))
        for p in axes(V,2)]
end
hamiltonian(B) = sum(b'b for b in B)

# Exterior-power isometry for the one-particle map W=[M;E].
# Lower d output bits are system modes; upper d bits are environment modes.
function fock_isometry(W::AbstractMatrix{T}) where T
    nout,d=size(W); V=zeros(T,1<<nout,1<<d)
    byn=[combinations(nout,n) for n in 0:d]
    for b in 0:(1<<d)-1
        cols=[i for i in 1:d if b & (1<<(i-1)) != 0]
        for rows in byn[length(cols)+1]
            target=sum(1<<(j-1) for j in rows; init=0)
            V[target+1,b+1]=isempty(cols) ? one(T) : det(W[rows,cols])
        end
    end
    V
end

function channel_observable(O,V,d)
    s=1<<d; out=zeros(eltype(O),s,s)
    for env in 0:(1<<d)-1
        block=@view V[(env*s+1):((env+1)*s),:]
        out += block' * O * block
    end
    out
end

# R1 has one environment fermion; R2 has two. Their squares form channel variance.
function channel_noise(c,ps,V,M,E)
    a=[sum(M[i,j]*c[j] for j in eachindex(c)) for i in eachindex(c)]
    BM=annihilator_pairs(a,ps,V)
    d=length(c); D=size(c[1],1)
    R1=[zeros(eltype(M),D,D) for i in 1:d]
    R2=[zeros(eltype(M),D,D) for _ in ps]
    for p in axes(V,2), (aidx,(j,k)) in enumerate(ps)
        coeff=V[aidx,p]
        iszero(coeff) && continue
        for i in 1:d
            R1[i] += coeff*(E[i,j]*a[k]' - E[i,k]*a[j]')*BM[p]
        end
        for (eidx,(i,l)) in enumerate(ps)
            R2[eidx] += coeff*(E[i,j]*E[l,k]-E[i,k]*E[l,j])*BM[p]
        end
    end
    H=hamiltonian(BM)
    H, sum(r'r for r in R1), sum(r'r for r in R2)
end

function gap_and_support(H; tol=1e-9)
    F=eigen(Hermitian(H)); good=findall(>(tol),F.values)
    isempty(good) && error("No positive spectrum")
    F.values[good[1]],F.vectors[:,good]*Diagonal(1 ./sqrt.(F.values[good]))
end

function exact_test()
    T=Rational{BigInt}; d=3; c=fermions(d,T); ps=combinations(d,2)
    # Rank-two rational projector; second pair overlaps in one-particle support.
    V=T[1 0; 0 3//5; 0 4//5]
    @test V'V == Matrix{T}(I,2,2)
    B=annihilator_pairs(c,ps,V); H0=hamiltonian(B)
    M=diagm(T[3//5,5//13,15//17]); E=diagm(T[4//5,12//13,8//17])
    @test M'M+E'E == Matrix{T}(I,d,d)
    W=fock_isometry(vcat(M,E))
    @test W'W == Matrix{T}(I,1<<d,1<<d)
    H,N1,N2=channel_noise(c,ps,V,M,E)
    PH=channel_observable(H0,W,d)
    PH2=channel_observable(H0*H0,W,d)
    @test PH == H
    @test PH2 == H*H+N1+N2
    println("EXACT_RATIONAL channel(Phi(H)) and channel-variance identities: PASS")
end

function floating_tests()
    Random.seed!(20261016)
    println("d,Q,requested_delta,actual_delta,base_gap,filtered_gap,relative_noise,noise_bound,max_channel_residual")
    for d in 3:6
        Q=d-1; c=fermions(d); ps,V=sphere_pairs(Q)
        H0=hamiltonian(annihilator_pairs(c,ps,V)); g0,_=gap_and_support(H0)
        for del in (0.001,0.01,0.05,0.2)
            U=Matrix(qr(randn(d,d)).Q)
            losses=del .* collect(range(0.2,1.0,length=d))
            M=U*Diagonal(sqrt.(1 .-losses))*U'
            E=U*Diagonal(sqrt.(losses))*U'
            delta=opnorm(I-M*M)
            H,N1,N2=channel_noise(c,ps,V,M,E)
            gf,T=gap_and_support(H)
            relnoise=eigmax(Hermitian(T'*(N1+N2)*T))
            bound=28delta+delta^2 # Safe all-Q analytic Schur constant (<28).
            @test relnoise <= bound+1e-9
            @test eigmin(Hermitian(delta^2*H-N2)) >= -1e-9
            @test gf >= g0-bound-1e-9
            F0=eigen(Hermitian(H0)); FM=eigen(Hermitian(H))
            z0=findall(<(1e-9),F0.values); zm=findall(<(1e-9),FM.values)
            @test length(z0) == length(zm)
            GammaInv=fock_isometry(inv(M))
            @test norm(H*GammaInv*F0.vectors[:,z0],Inf) < 1e-8
            W=fock_isometry(vcat(M,E))
            PH=channel_observable(H0,W,d)
            PH2=channel_observable(H0*H0,W,d)
            residual=max(norm(PH-H,Inf),norm(PH2-H*H-N1-N2,Inf),norm(W'W-I,Inf))
            @test residual < 1e-9
            @printf("%d,%d,%.6g,%.10g,%.10g,%.10g,%.10g,%.10g,%.3e\n",d,Q,del,delta,g0,gf,relnoise,bound,residual)
        end
    end
end

function complex_test()
    Random.seed!(5173)
    d=4; c=fermions(d,ComplexF64); ps,Vr=sphere_pairs(d-1)
    V=ComplexF64.(Vr); H0=hamiltonian(annihilator_pairs(c,ps,V))
    U=Matrix(qr(randn(ComplexF64,d,d)).Q)
    M=U*Diagonal(sqrt.([0.9,0.8,0.7,0.6]))*U'
    E=U*Diagonal(sqrt.([0.1,0.2,0.3,0.4]))*U'
    H,N1,N2=channel_noise(c,ps,V,M,E)
    W=fock_isometry(vcat(M,E))
    PH=channel_observable(H0,W,d)
    PH2=channel_observable(H0*H0,W,d)
    residual=max(norm(PH-H,Inf),norm(PH2-H*H-N1-N2,Inf),norm(W'W-I,Inf))
    @test residual < 1e-10
    println("COMPLEX_HERMITIAN filter channel identity: PASS; residual=",residual)
end

BLAS.set_num_threads(1)
@testset "Fermionic channel transfer" begin
    exact_test()
    floating_tests()
    complex_test()
end
