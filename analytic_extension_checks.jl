#!/usr/bin/env julia
# Independent analytic-audit support. Standard libraries; stdout only.
# These checks do not replace the all-K, Schur, or domain proofs in the .md files.
using LinearAlgebra, Test, Printf
const QQ = Rational{BigInt}
q(a,b=1)=QQ(big(a),big(b))

function simpson(f,a,b,n)
    @assert iseven(n)
    h=(b-a)/n
    h/3*(f(a)+f(b)+4sum((f(a+j*h) for j=1:2:n-1); init=0.0)+2sum((f(a+j*h) for j=2:2:n-2); init=0.0))
end

# Upper bound on 2 integral_0^infty |<m|D(sqrt(t))|n>| dt.
# Laguerre coefficients are replaced by their absolute values, the factorial
# square root by <=1, and odd powers of sqrt(t) by AM-GM. All arithmetic exact.
function displacement_integral_upper(m,n)
    a,b=minmax(m,n); d=b-a
    ans=q(0)
    for j=0:a
        coeff=q(binomial(big(b),a-j),factorial(big(j)))
        if iseven(d)
            e=j+div(d,2)
            ans += coeff*big(2)^(e+2)*factorial(big(e))
        else
            e=j+div(d,2)
            ans += coeff/2*(big(2)^(e+2)*factorial(big(e))+
                            big(2)^(e+3)*factorial(big(e+1)))
        end
    end
    ans
end

function annihilation4(j)
    c=zeros(QQ,16,16)
    bit=1<<(j-1)
    for state=0:15
        if state&bit != 0
            c[(state ⊻ bit)+1,state+1]=isodd(count_ones(state&(bit-1))) ? -1 : 1
        end
    end
    c
end

@testset "Revised Schur and finite-Slater analytic audit" begin
    @test q(14)^2 > q(8)^2*q(3)
    # The tail after L is bounded using sqrt(t^2+4)<=t+2.
    L=60.0
    c=2simpson(t->exp(-t/2)*sqrt(t*t+4),0.0,L,200000)
    tail=4*(L+4)*exp(-L/2)
    @test c+tail < 8sqrt(3)
    @printf("Plane nuclear-overlap integral (floating diagnostic): %.15f\n",c)
    @printf("Rigorous analytic tail formula beyond L=60: %.6g (floating evaluation)\n",tail)
    @printf("Exact usable constant C=14; analytic upper 8sqrt(3)=%.15f\n",8sqrt(3))
    for Q=1:1000
        # Algebraic expression squared; avoids certifying with floats.
        cs2=q(4*(2Q-1)^2,Q^2)*q(12Q^2+8,(Q+2)*(Q+4))
        @test cs2 < 192
    end
    @test simpson(s->2.0,0.0,1.0,2)==2
    @test q(3)*q(3,2)==q(9,2) # Q=2 nuclear kernel 2-s.

    # |2 wedge 3> in center/relative oscillator basis:
    # sqrt(1/8)|4,1> - (1/2)|2,3> + sqrt(5/8)|0,5>.
    @test q(1,8)+q(1,4)+q(5,8)==1
    @test q(7,16)^2-q(11,64)==q(5,256)
    beta=(7+2sqrt(11))/16
    K=[9/16 0 sqrt(10)/8; 0 1/8 0; sqrt(10)/8 0 5/16]
    @test isapprox(eigmax(Symmetric(K)),beta; atol=1e-14)
    @test all(eigvals(Symmetric(K)).>0)
    @test beta < 1
    Cslater=sum(displacement_integral_upper(m,n) for m=0:3,n=0:3)/2
    @test Cslater==q(336)
    println("Rank-two same-LLL family p=(|0 wedge 1>+|2 wedge 3>)/sqrt(2):")
    println("  beta=(7+2sqrt(11))/16 = ",beta)
    println("  explicit rational Schur bound (deliberately loose) C=",Cslater)
    println("  Reference full-Fock gap for this new pair operator: NOT ESTABLISHED.")

    # A genuinely nondecomposable family with an exactly proved reference gap.
    # Disjoint four-mode cells, B=(c2*c1+c4*c3)/sqrt(2).
    cs=[annihilation4(j) for j=1:4]
    A=cs[2]*cs[1]+cs[4]*cs[3]
    H=A'*A/2
    Id=Matrix{QQ}(I,16,16)
    @test H*(H-Id/2)*(H-Id)==zeros(QQ,16,16)
    @test tr(H)==4
    @test tr(H*H)==3
    println("Disjoint four-mode cells, exact rational local certificate:")
    println("  H(H-I/2)(H-I)=0; spectrum multiplicities 0:10, 1/2:4, 1:2.")
    println("  Any number of cells: gamma0=1/2, beta=1, C=2; transfer gap >=1/2-2delta-delta^2.")
end
