#!/usr/bin/env julia
# Direct full-Fock checks of the nuclear-norm two-frame Gram majorant.
# Does not include or modify independent_channel_audit.jl.
using LinearAlgebra, Random, Printf, Test
BLAS.set_num_threads(1)
const NUCLEAR_SEED=2026101619
function annihilation_matrices(d)
    D=2^d
    [begin
        c=zeros(ComplexF64,D,D)
        for occupation in 0:D-1
            flag=1<<(j-1)
            if !iszero(occupation & flag)
                c[(occupation ⊻ flag)+1,occupation+1]=
                    isodd(count_ones(occupation & (flag-1))) ? -1 : 1
            end
        end
        c
    end for j in 1:d]
end
creation(c,a)=sum(a[j]*c[j]' for j in eachindex(c))
function R_direct(c,M,U)
    u,v=U[:,1],U[:,2]
    kron(u,creation(c,M*v))-kron(v,creation(c,M*u))
end
haar_unitary(rng,d)=Matrix(qr(randn(rng,ComplexF64,d,d)).Q)
function positive_contraction(rng,d;near_singular=false)
    Q=haar_unitary(rng,d)
    ev=0.02 .+0.98rand(rng,d)
    near_singular && (ev[1]=1e-7;ev[end]=1.0)
    Q*Diagonal(ev)*Q'
end
const STATS=Dict("max_residual"=>0.0,"max_norm_over_bound"=>0.0,"max_commutator"=>0.0)
function audit_case(name,M,U,V)
    d=size(M,1);c=annihilation_matrices(d);tol=2e-12
    @test norm(U'U-I)<tol && norm(V'V-I)<tol
    @test norm(M-M')<tol && eigmin(Hermitian(M))>=-tol && opnorm(M)<=1+tol
    RU,RV=R_direct(c,M,U),R_direct(c,M,V)
    G=RU'RV
    overlap=U'V;f=svd(overlap)
    A,B=f.U,f.V
    Up,Vp=U*A,V*B
    RUp,RVp=R_direct(c,M,Up),R_direct(c,M,Vp)
    diagonal_res=norm(Up'Vp-Diagonal(f.S))
    determinant_res=max(norm(RUp-det(A)*RU),norm(RVp-det(B)*RV))
    phase=conj(det(A))*det(B)
    gram_res=norm(RUp'RVp-phase*G)
    # Diagonal SVD overlap removes both off-diagonal terms exactly.
    expected=f.S[1]*(creation(c,M*Up[:,2])'*creation(c,M*Vp[:,2]))+
             f.S[2]*(creation(c,M*Up[:,1])'*creation(c,M*Vp[:,1]))
    expansion_res=norm(RUp'RVp-expected)
    residual=max(diagonal_res,determinant_res,gram_res,expansion_res)
    @test residual<tol
    nuclear=sum(f.S);actual=opnorm(G)
    @test actual<=nuclear+tol
    # Also check the explicit 2x2 trace-norm invariant used in the plane bound.
    @test abs(nuclear^2-(sum(abs2,overlap)+2abs(det(overlap))))<tol
    # Extend each two-frame basis change to a one-particle unitary. These
    # generally do NOT commute with M; no commutation enters the test.
    WU=U*A*U'+(I-U*U');WV=V*B*V'+(I-V*V')
    commutator=max(norm(M*WU-WU*M),norm(M*WV-WV*M))
    STATS["max_residual"]=max(STATS["max_residual"],residual)
    STATS["max_commutator"]=max(STATS["max_commutator"],commutator)
    nuclear>tol && (STATS["max_norm_over_bound"]=max(STATS["max_norm_over_bound"],actual/nuclear))
    @printf("%s,d=%d,gram_norm=%.12g,nuclear_bound=%.12g,residual=%.3e,noncommutation=%.3e\n",
        name,d,actual,nuclear,residual,commutator)
    (;actual,nuclear)
end
println("NUCLEAR_OVERLAP_AUDIT Julia=",VERSION," seed=",NUCLEAR_SEED," BLAS_threads=",BLAS.get_num_threads())
println("Target: ||R_U'R_V|| <= ||U'V||_1; R_U=u tensor c*(Mv)-v tensor c*(Mu)")
@testset "Nuclear overlap Gram bound" begin
    rng=MersenneTwister(NUCLEAR_SEED)
    for d in 3:6, trial in 1:6
        U=haar_unitary(rng,d)[:,1:2];V=haar_unitary(rng,d)[:,1:2]
        M=positive_contraction(rng,d;near_singular=(trial==6))
        audit_case("random_$trial",M,U,V)
    end
    for d in (3,6)
        U=haar_unitary(rng,d)[:,1:2]
        r=audit_case("coincident_saturates",Matrix{ComplexF64}(I,d,d),U,U)
        @test abs(r.actual-2)<2e-12 && abs(r.nuclear-2)<2e-12
    end
    for d in (4,6)
        Q=haar_unitary(rng,d)
        r=audit_case("orthogonal_zero",positive_contraction(rng,d),Q[:,1:2],Q[:,3:4])
        @test r.actual<2e-12 && r.nuclear<2e-12
    end
    d=3;Q=haar_unitary(rng,d)
    r=audit_case("one_direction_intersection",Matrix{ComplexF64}(I,d,d),Q[:,[1,2]],Q[:,[2,3]])
    @test abs(r.actual-1)<2e-12 && abs(r.nuclear-1)<2e-12
    d=4;U=haar_unitary(rng,d)[:,1:2]
    A=ComplexF64[0 im;1 0]
    audit_case("same_plane_complex_phase",positive_contraction(rng,d),U,U*A)
    @test STATS["max_commutator"]>0.1
end
println("CASES=30 SUMMARY=",STATS)
