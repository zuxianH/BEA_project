function plot_branch_summary(br)
    step_vals = [pt.step for pt in br.branch]
    p_vals = [pt.param for pt in br.branch]
    arc_vals = [abs(pt.ds) for pt in br.branch]
    x_vals = [pt.x1 for pt in br.branch]  # state values
    diff_x_vals = diff(x_vals)


    plot(
        plot(p_vals, x_vals, title="solution vs λ0", xlabel="λ0", ylabel="solution",seriestype=:scatter),
        plot(p_vals[2:end], diff_x_vals, title="Δsolution vs λ0", xlabel="λ0", ylabel="Δsolution",seriestype=:scatter),
        plot(arc_vals,p_vals, title="λ0 vs Arc Length", ylabel="λ0", xlabel="Arc Length"),
        plot(step_vals, p_vals, title="Step vs λ0", xlabel="Step", ylabel="λ0"),
        plot(step_vals, arc_vals, title="Step vs λ0", xlabel="Step", ylabel="Arc Length"),
        size=(1000,500),legend=false,
        layout=(1,5)
    )
end

# Extract the last solution
function extract_last_solution(br)
    last_point = br.branch[end]
    get_last_solution = collect(values(last_point)[1:length(u0)])
    return get_last_solution
end


# Export the last solution to a CSV file
function export_last_solution_to_csv(br, filename="get_last_solution.csv")
    last_point = br.branch[end]
    get_last_solution = collect(values(last_point)[1:length(u0)])
    df_out = DataFrame(var = string.(vars[1:end-1]), b_final_value = get_last_solution)
    CSV.write(filename, df_out)
end

# Export the entire branch to a CSV file
function export_branch_to_csv(br, filename="all_branch.csv")
    branch_df = DataFrame([pt for pt in br.branch])
    for col in names(branch_df)
        if eltype(branch_df[!, col]) == Nothing
            branch_df[!, col] = Any[branch_df[!, col]...]  # convert to Any
        end
        replace!(branch_df[!, col], nothing => missing)
    end
    CSV.write(filename, branch_df)
end

# Plot the solution against the parameter values for a given variable or index
function plot_solution(br, var_or_index)
    p_vals = [pt.param for pt in br.branch]
    plt = plot(
        title="solution vs λ",
        xlabel="λ",
        ylabel="value",
        legend=:outerright
    )
    if isa(var_or_index, Symbol) || isa(var_or_index, Int)
        var_or_index = [var_or_index]
    end
    for v in var_or_index
        x_vals = isa(v, Symbol) ? [getfield(pt, v) for pt in br.branch] : [collect(values(pt))[v] for pt in br.branch]
        plot!(plt, p_vals, x_vals; seriestype=:scatter, label=string(v))
    end
    return plt
end


######################################################################

function load_data_and_initialize(path::String)
    global vars, vars_init, expr_funcs,df
    # Load the CSV file
    load_initial_data = CSV.read(path, DataFrame)
    # Extract the expressions and variable names
    df = load_initial_data.expression
    vars = Symbol.(vcat(load_initial_data.var, "h"))
    #vars_init = BigFloat.(replace.(load_initial_data.Initialvar, r"`.*" => ""))
    initialvar_processed = replace.(string.(load_initial_data.Initialvar), r"\*10\^" => "e")
    vars_init = BigFloat.(initialvar_processed)
    # Load the expressions from the CSV file
    expr_funcs = [
        eval(Expr(:->, Expr(:tuple, vars...), Meta.parse(expr)))
        for expr in df
    ]
end


# Define the general evaluation function
function G(u, p)
    args = vcat(u, p)
    return [f(args...) for f in expr_funcs]  
end;


function make_opts(newton_tol,dsmax_tol)
    return ContinuationPar(
        ds = my_ds, # step size
        dsmin = my_dsmin, # minimum step size
        dsmax = dsmax_tol, # maximum step size
        p_min = 0., # minimum value of the parameter
        p_max = lambda0, # maximum value of the parameter
        max_steps = 1e5, # maximum number of steps
        newton_options = NewtonPar(tol = newton_tol,
                    max_iterations = my_newton_iterations,
                    verbose = false),
        detect_bifurcation = 0, 
        detect_event = 0,
        a = my_a, 
        detect_loop = false
    )
end


function run_continuation_with_tol(prob, dsmax, method; dp_tol=0.3, initial_tol=1e-12, max_tol=1e-7)
    my_tol = initial_tol   # initial newton tolerance
    br = nothing
    while true
        br = continuation(
            prob, # defined problem
            method, # method to use e.g. PALC()
            make_opts(my_tol, dsmax), 
            normC = norminf,  # norm function
            callback_newton = (state; kwargs...) -> cb(state; kwargs..., dp=dp_tol), # callback function
            verbosity = 0 # verbosity level (0 to 3)
            )
        if br.sol[end].p == 0

            break
        elseif my_tol >= max_tol
            error("Failed to reach br.sol[end].p == 0 even at max tolerance.")
        else
            @warn "br.sol[end].p != 0 with tol=$my_tol, increasing tolerance and retrying..."
            println(br.sol[end].p)
            my_tol *= 10
        end
    end
    return br
end



function run_lazy(my_dp_tol)
    run = run_continuation_with_tol(
        prob, 
        1e100, # dsmax 
        PALC(tangent = Bordered(),θ=0.5), 
        #MoorePenrose(method = BifurcationKit.iterative),
        dp_tol=my_dp_tol, 
        initial_tol=my_initial_tol, 
        max_tol=1e-2)
    return run
end

function my_tol_x(indices)
    if length(indices) == 0
        return 0.01  # Default tolerance if no indices are provided
    else
        return my_dx_tol  # Adjust as needed for the specific indices
    end
end

function cb(state; dp, kwargs...)
    _x        = get(kwargs, :z0, nothing)
    fromNewton = get(kwargs, :fromNewton, false)
    if !fromNewton && _x !== nothing
        dp_jump = abs(_x.p - state.p)
        dx_vals = abs.(_x.u[indices] .- state.x[indices])  # Compute differences for all indices
        tol_vals = my_tol_x(indices)                      # Get tolerances for all indices
        if any(dx_vals .> tol_vals) || dp_jump > dp       # Check if any dx exceeds tolerance or dp_jump is too large
            return false
        end
    end
    return true
end