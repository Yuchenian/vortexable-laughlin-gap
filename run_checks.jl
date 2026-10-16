#!/usr/bin/env julia
# Portable entry point. Every suite executes in a fresh Julia process.
using Dates, SHA
root=@__DIR__
stamp=Dates.format(now(UTC),dateformat"yyyymmddTHHMMSSsss")
out=joinpath(root,"results","rerun_"*stamp)
mkpath(out)
scripts=["channel_transfer_checks.jl","analytic_bound_checks.jl",
    "independent_channel_audit.jl","nuclear_overlap_checks.jl",
    "analytic_extension_checks.jl","extension_bound_checks.jl"]
open(joinpath(out,"environment.txt"),"w") do io
    println(io,"UTC ",stamp,"\nJulia ",VERSION,"\nOS ",Sys.KERNEL,"\nArchitecture ",Sys.ARCH)
    for name in vcat(["Project.toml","run_checks.jl"],scripts)
        println(io,bytes2hex(sha256(read(joinpath(root,name)))),"  ",name)
    end
end
println("AI-assisted draft; human verification incomplete.")
println("Finite checks do not establish a thermodynamic theorem.")
for script in scripts
    logfile=joinpath(out,script*".log")
    println("Running ",script)
    cmd=Cmd(vcat(Base.julia_cmd().exec,["--startup-file=no","--history-file=no",
        "--project="*root,joinpath(root,script)]))
    try
        open(logfile,"w") do io
            run(pipeline(cmd;stdout=io,stderr=io))
        end
    catch
        print(read(logfile,String))
        println(stderr,"FAILED: ",script,"; retained logs in ",relpath(out,root))
        rethrow()
    end
    for line in split(read(logfile,String),'\n')
        if occursin("Pass",line) || occursin(r"\|\s+\d+\s+\d+\s+",line)
            println(strip(line))
        end
    end
end
println("All six scripts exited successfully. Logs: ",relpath(out,root))
