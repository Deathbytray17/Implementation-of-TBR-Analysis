====TO BE RECORDED(TBR) ANALYSIS TOOL===

-Prerequisites include:
	Python 3.x
	lark-parser
	tkinter


HOW TO USE:
	1. install the prerequisite libraries
	2. run the script
	3. A GUI will appear

Using the GUI:
	Enter your code: Paste or type your C-like source code into the text area.
	Input Variables: Provide a comma-separated list of independent variable names (e.g., x, y).
	Output Variables: Provide a comma-separated list of dependent (output) variable names (e.g., result).
	

Results:
	After running, a pop-up window will display:
		-Instructions: A list of parsed assignment instructions.
		-Dependencies: Mapping of each variable to its input dependencies.
		-Varied Variables: Variables influenced by the independent inputs.
		-Useful Variables: Variables necessary to compute the outputs.
		-Active Variables: Intersection of varied and useful, plus control-dependent variables.
		-AdjU Variables: Variables required for adjoint usage.
		-Required Variables: Remaining variables after analysis.

=======>Variable PUSHes: PUSH messages for variables need to be recored.

		Control PUSHes: Control flow push messages for branches and loops.