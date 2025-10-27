include("bethe_functions.jl")
using IncompleteLU, LinearAlgebra, SparseArrays
using HomotopyContinuation

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

# change to desired SYT
my_SYT = "{{1, 2, 4, 6, 7, 8}, {3, 10, 11, 12, 14}, {5, 13, 17}, {9}, {15}, {16}}.csv"

# -------load and scale system and vars-----------------------
my_SYT = "initial_data.csv"
my_λ0 = Float64(CSV.read("$my_path/$my_SYT", DataFrame).lambda0[1])
load_problem_scale(my_SYT,my_λ0,1.)
my_scale_param = maximum(abs.(u0))
load_problem_scale(my_SYT,my_λ0,my_scale_param)
#norm(G(u0/my_scale_param,p0))
# -------------------------------------------------------------------------


# -------load system and vars to HomotopyContinuation-----------------------
# define variables 
myvars = [Symbol(string(var)) for var in [load_initial_data.var; "h"]]
# evaluate var
@eval @var $(myvars...)
# define expression 
my_expression = [eval(Meta.parse(df[k])) for k in 1:length(df)];
F = System(
    my_expression,
    variables = [Variable(Symbol(string(var))) for var in load_initial_data.var], 
    parameters = [h]
);
# -------------------------------------------------------------------------


# ---------extract name of previous result----------------------------------
# call syt in string
string_syt = load_initial_data.syt[1]
# maximal element of syt 
max_syt = maximum(parse.(Int, split(replace(string_syt, r"[^\d,]" => ""), ",")))
# define name of syt result 
find_filename = "result_$(string_syt).csv"
# -------------------------------------------------------------------------



if isfile("$my_path/$find_filename")
    println("File $find_filename already exists. Loading existing solutions.")
    df_out = CSV.read("$my_path/$find_filename", DataFrame)
    df_out.b_final_value
else
    println("File $find_filename does not exist. Proceeding with HomotopyContinuation.")

    if max_syt <=21
        start_solutions = [u0/my_scale_param]
        result = @time solve(
            F, 
            start_solutions; 
            start_parameters=p0, 
            target_parameters=[0.],
            show_progress= true,
            tracker_options = TrackerOptions(
                automatic_differentiation = 3, 
                terminate_cond = 1e50,
                extended_precision = true,
                parameters = :conservative
                #parameters=TrackerParameters(β_τ = 0.01, β_ω_p = 10.0) 
            )
        )

        
        if isempty(real_solutions(result))
            println("No real solutions found from HomotopyContinuation.")
            println("Start PALC")
            include("PALC_BAE.jl")
        else
            # Save the solutions to a CSV file with name result_<SYT>.csv
            df_out = DataFrame(var = string.(vars[1:end-1]), b_final_value = reduce(vcat, real_solutions(result)) * my_scale_param)
            file_path = "$my_path/result_$(load_initial_data.syt[1]).csv"
            CSV.write(file_path, df_out)
            reduce(vcat, real_solutions(result)) * my_scale_param
        end
    else 
        include("PALC_BAE.jl")
    end 

end


