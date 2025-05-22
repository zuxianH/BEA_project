using CSV, DataFrames,BifurcationKit,JLD2,Serialization,LinearAlgebra,Suppressor,ForwardDiff, Statistics,Plots
include("bethe_functions.jl")

dymamic_plot()

function load_problem(λ0::Float64)
    global my_SYT = "{{1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {2}, {3}}.csv"; 
    load_data_and_initialize("/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/saved_data/$my_SYT");
    # Define the bifurcation problem
    global lambda0 = λ0;
    global u0 = Float64.(vars_init)      
    global p0 = [lambda0];  
    # Print the norm of G at initial point to check how far we are from a solution
    #print("Residual norm at initial point: ", norm(G(u0,p0)));        
    global prob = BifurcationProblem(G, u0, p0,1; record_from_solution = (x, p; k...) -> (Tuple(x)));
end 

load_problem(1000.)
G(u0/my_scale_param,p0)

function load_problem_scale(λ0::Float64,scale_param::Float64)
    global my_SYT = "{{1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {2}, {3}}.csv"; 
    load_scale_data_and_initialize(scale_param,"/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/saved_data/$my_SYT");
    global lambda0 = λ0;
    global u0 = Float64.(vars_init)      
    global p0 = [lambda0];  
    # Print the norm of G at initial point to check how far we are from a solution
    global prob = BifurcationProblem(G, u0/scale_param, p0,1; record_from_solution = (x, p; k...) -> (Tuple(x)));
end 

my_scale_param = 1e6
load_problem_scale(1000.,my_scale_param)

function run_main()
    # Definition of default continuation parameters
    main_Opts = ParameterOpts( 
        -1e-3,        # ds: Initial step size (negative for reverse direction)
        1e20,         # dsmax: Maximum step size
        1e-4,         # dsmin: Minimum step size
        lambda0,      # lambda0: Maximum parameter value
        42,           # max_newton_iterations: Maximum iterations for Newton's method
        1e-7,         # newton_tol: Tolerance for Newton's method convergence
        0.1,         # a: damping factor
        true,         # verbose: Whether to print detailed information
    )

    global my_verbosity  = 2;

    global final_result = run_lazy(prob, 10. ,main_Opts)
    maximum_start_value = maximum(abs.(final_result.sol[1].x))
    minimal_start_value = minimum(abs.(final_result.sol[1].x))
    println("Maximum start value: ", maximum_start_value)
    println("Minimal start value: ", minimal_start_value)
    println("Ratio: ", maximum_start_value/minimal_start_value)
    println("parameter: ", getparams(final_result))
    println("Newton tolerance: ", final_result.contparams.newton_options.tol)
    println("Number of special points: ", length(final_result.specialpoint)-1)
    println("Step: ", final_result.step[end])
    println("Solution: ", extract_last_solution(final_result))
end

run_main()

# auto‐detect which component is smallest at the first branch point
u0_vals        = final_result.sol[1].x 
uend_vals      = final_result.sol[end].x
diff_first_last = abs.(uend_vals-u0_vals)
indices = findall(x -> x < 4, diff_first_last)
plot_solution(final_result,indices)

####################################
last_point = final_result.branch[end];
get_last_solution = collect(values(last_point)[1:length(u0)]) * my_scale_param
get_last_param = float(final_result.branch[end].param);
println("Norm λ=0: ", norm(G(get_last_solution,get_last_param)));
prob_reverse = BifurcationProblem(G, get_last_solution, get_last_param,1; record_from_solution = (x, p; k...) -> (Tuple(x)))
####################################
reverse_Opts = ParameterOpts( 
    1e-2,        # ds: Initial step size (negative for reverse direction)
    1e10,         # dsmax: Maximum step size
    1e-4,         # dsmin: Minimum step size
    lambda0,      # lambda0: Maximum parameter value
    42,           # max_newton_iterations: Maximum iterations for Newton's method
    1e-7,         # newton_tol: Tolerance for Newton's method convergence
    0.01,         # a: damping factor
    true,         # verbose: Whether to print detailed information
);
include("bethe_functions.jl")
reverse_result = run_lazy(prob_reverse, 10. ,reverse_Opts)



#=
reverse_result = continuation(
            prob_reverse,
            PALC(tangent = Bordered(),θ=0.5),
            make_opts(reverse_Opts),
            normC = norminf,
            callback_newton = (state; kwargs...) -> cb(state; kwargs..., dp=1),
            verbosity = 2
        )
=#

println("Norm of diff initial and reverse: ", norm(reverse_result.sol[end].x .-u0))

plot(reverse_result)


plot(
    plot_solution(final_result,indices),
    plot_solution(reverse_result,indices)
)