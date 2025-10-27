include("bethe_functions.jl")
using IncompleteLU, LinearAlgebra, SparseArrays
x_error_list=[]
my_path = "/home/zuxian/Documents/BAE/saved_data"

function load_problem_scale(my_SYT, λ0::Float64,scale_param::Float64)
    load_scale_data_and_initialize(scale_param,"$my_path/$my_SYT");
    load_jacobian(scale_param)
    global u0 = Float64.(vars_init)      
    global p0 = [λ0];  
    global prob = BifurcationProblem(
    G, u0/scale_param, p0,1; 
    J = (x, p) -> (scaled_Jac(x, p)),
    record_from_solution = (x, p; k...) -> (Tuple(x))
    );
end 



my_SYT = "{{1, 3, 6, 9}, {2, 5, 7, 10}, {4, 11, 13}, {8, 12, 14}}.csv"

# -------load and scale system and vars-----------------------
my_SYT = "initial_data.csv"
my_λ0 = Float64(CSV.read("$my_path/$my_SYT", DataFrame).lambda0[1])
load_problem_scale(my_SYT,my_λ0,1.)
my_scale_param = maximum(abs.(u0))
load_problem_scale(my_SYT,my_λ0,my_scale_param)
norm(G(u0/my_scale_param,p0))
# -------------------------------------------------------------------------

ls = GMRESIterativeSolvers(
    N =  length(u0)+1,
    #Pl = ilu(sparse(scaled_Jac(u0/my_scale_param, p0)), τ = 0.001)
    )

# Initialization 
ind_sol_need_check = collect(1:length(u0))
new_tol = 1.

function cb(state; dp, kwargs...)
    _x        = get(kwargs, :z0, nothing)
    fromNewton = get(kwargs, :fromNewton, false)
    if !fromNewton && _x !== nothing
        dp_jump = abs(_x.p - state.p)
        dx_vals = abs.(_x.u[ind_sol_need_check] .- state.x[ind_sol_need_check])  # Compute differences for all indices
        tol_vals = new_tol                      # Get tolerances for all indices
        if all(dx_vals .> tol_vals) || dp_jump > dp       # Check if any dx exceeds tolerance or dp_jump is too large
            return false
        end
    end
    return true
end

function run_main()
    # Definition of default continuation parameters
    global main_Opts = ParameterOpts( 
        -1e-3,        # ds: Initial step size (negative for reverse direction)
        1e20,         # dsmax: Maximum step size
        1e-4,         # dsmin: Minimum step size
        my_λ0,        # lambda0: Maximum parameter value
        0.,
        100,          # max_newton_iterations: Maximum iterations for Newton's method
        1e-7,         # newton_tol: Tolerance for Newton's method convergence
        0.007,        # a: damping factor
        false,        # verbose: Whether to print detailed information
    )
    global my_verbosity  = 0;
    return run_lazy(prob, 70. ,main_Opts)
end


#=
function run_main()
    # Definition of default continuation parameters
    global main_Opts = ParameterOpts( 
        1e-3,        # ds: Initial step size (negative for reverse direction)
        1e20,         # dsmax: Maximum step size
        1e-4,         # dsmin: Minimum step size
        100.,        # lambda0: Maximum parameter value
        my_λ0,
        100,          # max_newton_iterations: Maximum iterations for Newton's method
        1e-7,         # newton_tol: Tolerance for Newton's method convergence
        0.01,        # a: damping factor
        false,        # verbose: Whether to print detailed information
    )
    global my_verbosity  = 0;
    return run_lazy(prob, 50. ,main_Opts)
end
=#

run_dummy = @time run_main()



r_squared_table = calculate_r_squared_table(run_dummy)
low_r_squared_components = r_squared_table[r_squared_table.R_squared .< 0.6, :]
# Check if low_r_squared_components.Component is empty
if isempty(low_r_squared_components.Component)
    ind_sol_need_check = collect(1:length(u0))  # Use all indices if Component is empty
else
    ind_sol_need_check = low_r_squared_components.Component  # Use the specified components
end



abs_diff = [abs(run_dummy.sol[end].x[i] - run_dummy.sol[1].x[i]) for i in ind_sol_need_check]
new_tol = abs_diff / 200


ratio = 0.0  # Initialize ratio
my_while_tol = 500
step_size = 1000
max_iterations = 10  # Maximum number of iterations
iteration_count = 0  # Initialize iteration counter

while ratio <= 0.99 && iteration_count < max_iterations
    global new_tol = abs_diff / my_while_tol
    # Perform continuation
    global final_result = run_main()
    
    # Assuming final_result.branch.itnewton is an array
    itnewton_values = final_result.branch.itnewton

    # Count occurrences of 0, 1, and 2
    count_0 = count(x -> x == 0, itnewton_values)
    count_1 = count(x -> x == 1, itnewton_values)
    count_2 = count(x -> x == 2, itnewton_values)

    # Compute the total count
    total_count = count_0 + count_1 + count_2

    # Compute the ratio
    global ratio = total_count / length(itnewton_values)
    println("Iteration: ", iteration_count + 1, " | ratio: ", ratio, " | norm: ", norm(extract_last_solution(final_result) * my_scale_param), " | step: ", final_result.step[end])
    
    # Update new_tol dynamically
    global my_while_tol += step_size

    # Increment the iteration counter
    global iteration_count += 1
end

#df_out = DataFrame(var = string.(vars[1:end-1]), b_final_value = extract_last_solution(final_result)*my_scale_param)
# Assuming load_initial_data is a variable with a field `syt`
#file_path = "/home/zuxian/Documents/BAE_Project/TestFindMinimun/JuliaBifurcation/saved_data/result_$(load_initial_data.syt[1]).csv"
#CSV.write(file_path, df_out)


println("Number of Step: ", final_result.step[end])
println("ind_sol_need_check: ", ind_sol_need_check)
println("Param: ", [final_result.param[1],final_result.param[end]])
println("Solution: ", extract_last_solution(final_result)*my_scale_param)
println("-----------------------------------------------------")


function get_final_solution_or_message(final_result)
    if final_result.param[end] == 0
        return extract_last_solution(final_result) * my_scale_param
    else
        return "no solution is founded"
    end
end

function get_final_solution_or_message(final_result, iteration_count, max_iterations)
    if iteration_count == max_iterations
        return "no solution is founded"
    elseif final_result.param[end] == 0
        return extract_last_solution(final_result) * my_scale_param
    else
        return "no solution is founded"
    end
end


# use it
#get_final_solution_or_message(final_result)

get_final_solution_or_message(final_result, iteration_count, max_iterations)
