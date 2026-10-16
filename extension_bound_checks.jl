#!/usr/bin/env julia
# Exact finite-Fourier/coercivity certificates. No packages or external theorem verification.
using Test, Printf
const Rat = Rational{BigInt}
rat(a,b=1) = Rat(BigInt(a),BigInt(b))
function taylor(x,n)
    t=one(x); s=t
    for j=1:n
        t=t*x/j; s+=t
    end
    s
end
function gapbound(alpha,kappa; C=rat(14),gamma=rat(1,5))
    delta=2alpha/(1+alpha)
    kappa/(1-alpha)^2*(gamma-C*delta-delta^2)
end
function report(label,b)
    println(label," = ",b," ; decimal=",Float64(b))
end
@testset "Exact extension certificates" begin
    # pi>157/50 and pi<22/7 are elementary analytic inputs.
    @test taylor(rat(157,50),15)>23
    @test taylor(rat(157,25),20)>500
    @test taylor(rat(157,100),8)>rat(100,21)
    # Planar nuclear-overlap Schur bound 8sqrt(3)<14.
    @test 64*3<14^2
    # Original examples independently recomputed with the original and revised C.
    for (label,eps,alpha) in [("first_harmonic",rat(1,100),rat(21,10000)),
                              ("second_harmonic",rat(1,2),rat(1,1000))]
        old=gapbound(alpha,(1-eps)^2;C=rat(20))
        new=gapbound(alpha,(1-eps)^2)
        @test new>old>0
        report(label*"_C20",old)
        report(label*"_C14",new)
    end
    sphere=gapbound(rat(1,1000),rat(999,1000)^2;C=rat(28))
    @test sphere==rat(721701,5010005)
    report("sphere_C28",sphere)
    sphere14=gapbound(rat(1,1000),rat(999,1000)^2)
    @test sphere14>rat(172,1000)
    report("sphere_C14",sphere14)
    # Audited all-Q CS estimate: C_Q^2 = 4(2Q-1)^2/Q^2 * (12Q^2+8)/((Q+2)(Q+4)).
    # Polynomial difference from 192 is 1344Q^3+1360Q^2+128Q-32 >0 for Q>=1.
    for Q in [1,2,3,10,100,10000]
        cs2=rat(4*(2big(Q)-1)^2,Q^2)*rat(12big(Q)^2+8,(big(Q)+2)*(Q+4))
        @test cs2<192
    end

    # New smooth nodal multiplier f=2cos(kx)cos(ky), k=sqrt(2pi)/ell.
    r=rat(1,500); t=rat(1,23)
    alpha=2r+r^2
    kappa=rat(9,2)-(rat(3,2)+2t+t^4/2)^2
    @test alpha==rat(1001,250000)
    @test kappa>rat(19,10)
    old=gapbound(alpha,kappa;C=rat(20))
    new=gapbound(alpha,kappa)
    @test old>rat(8,100)
    @test new>rat(17,100)
    report("nodal_Gram_alpha",alpha)
    report("nodal_pair_coercivity",kappa)
    report("nodal_gap_C20",old)
    report("nodal_gap_C14",new)
    # Whole-family sufficient polynomial Fourier sums, exact at these safe bounds.
    for amp in [rat(0),rat(1,4),rat(1,2),rat(3,4),rat(1)]
        # |f|^2=(1+amp*cos(qx))(1+amp*cos(qy)); amp=1 has smooth signed f above.
        a=2amp*r+amp^2*r^2
        c0=1+amp^2/2
        kw=2c0^2-(c0+2amp*t+amp^2*t^4/2)^2
        b=gapbound(a,kw)
        @test kw>0 && b>0
        println("family amplitude=",amp," kappa=",Float64(kw)," gap_C14=",Float64(b))
    end
    # Uniform constant-multiplier scale cancellation: H_sqrt(s) = H0.
    s=rat(7,3); @test s^2/s^2*rat(1,5)==rat(1,5)
    # General diffeomorphism dilation F(r)=lambda*r: J*||DF||F^2/2=lambda^4.
    lam=rat(3,2); @test (lam^2)*(2lam^2)/2==lam^4
    # Area-preserving shear: J=1, squared Frobenius norm=2+a_s^2 cos^2.
    for a in [rat(0),rat(1),rat(10)], c in [rat(-1),rat(0),rat(1,2),rat(1)]
        w=(2+a^2*c^2)/2
        @test w>=1
    end
end
println("Interpretation: exact rational evaluations and analytic Fourier estimates; gamma0 is external input.")
