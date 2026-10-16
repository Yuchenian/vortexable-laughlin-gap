#!/usr/bin/env julia
# Exact arithmetic checks for constants/examples in PROOF_DRAFT.md.
# These checks do not re-verify the external Laughlin SDP certificate.
using Test, Printf
const QQ=Rational{BigInt}
q(a,b=1)=QQ(BigInt(a),BigInt(b))

function exp_partial(x,n)
    term=one(x); ans=term
    for j in 1:n
        term*=x/j; ans+=term
    end
    ans
end

function bound(eps::QQ, abar::QQ; C=q(20), gamma=q(1,5))
    @assert 0 <= eps < 1 && 0 <= abar < 1
    delta=2abar/(1+abar)
    pref=((1-eps)/(1-abar))^2
    pref*(gamma-C*delta-delta^2)
end

function simpson(f,a,b,n)
    @assert iseven(n)
    h=(b-a)/n
    h/3*(f(a)+f(b)+4sum(f(a+j*h) for j in 1:2:n-1)+2sum(f(a+j*h) for j in 2:2:n-2))
end

@testset "Exact normalization and analytic bounds" begin
    # Elementary external inequalities used here: 157/50 < pi < 22/7,
    # and e > 1+1+1/2+1/6 = 8/3.
    @test q(251,100)^2 > q(44,7)
    @test q(49,80)^2*q(8,3) > 1
    @test 4q(251,100)+16q(49,80) < 20
    @test q(3,2)^2 > 2
    @test 16+8q(3,2) == 28 # sphere C <16+8sqrt(2)<28.

    # exp(pi/2)>100/21 and exp(2pi)>500, via finite rational Taylor sums.
    @test exp_partial(q(157,100),8) > q(100,21)
    @test exp_partial(q(157,25),20) > 500

    # Planar coherent pair frame: each relative-momentum-one CM block is
    # a normalized vector, not twice a projector or half a projector.
    for K in 1:40
        normsq=sum(q((K-2i)^2)*q(factorial(big(K-1)),big(2)^(K-1)*factorial(big(i))*factorial(big(K-i)))
                   for i in 0:fld(K-1,2))
        @test normsq == 1
    end

    C=4sqrt(2pi)+16exp(-0.5)
    f(u)=4u*exp(-u*u/2)*(1+2u+abs(1-u*u))
    direct=simpson(f,0.0,1.0,20000)+simpson(f,1.0,14.0,200000)
    @test abs(C-direct) < 1e-9
    @printf("PLANAR_SCHUR_C = %.15f; direct integral = %.15f; safe rational C = 20\n",C,direct)

    eps=q(1,100); a=eps*q(21,100)
    b1=bound(eps,a)
    @test b1 == q(9448394202000,82643899175161)
    @test b1 > q(114,1000)
    println("PLANE_FUNDAMENTAL eps=1/100, q^2*lB^2=2*pi: ",b1," = ",Float64(b1))

    eps=q(1,2); a=eps*q(1,500)
    b2=bound(eps,a)
    @test b2 > q(4,100)
    println("PLANE_SECOND_HARMONIC eps=1/2, q^2*lB^2=8*pi: ",b2," = ",Float64(b2))

    eps=q(1,1000); b3=bound(eps,eps; C=q(28))
    @test b3 > q(144,1000)
    println("SPHERE_ARBITRARY_PATTERN |f^2-1|<=1/1000: ",b3," = ",Float64(b3))

    @test bound(q(0),q(0)) == q(1,5)
    println("\neps,harmonic,r_upper,analytic_gap_lower_bound")
    for eps in [q(1,1000),q(1,100),q(1,50),q(1,10),q(1,2),q(9,10)]
        for (n,r) in [(1,q(21,100)),(2,q(1,500))]
            bb=bound(eps,eps*r)
            @printf("%.6g,%d,%.6g,%.12g\n",Float64(eps),n,Float64(r),Float64(bb))
        end
    end
end
