package org.scribble.ext.go.core.codegen.statetype;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import org.scribble.ast.Module;
import org.scribble.ast.ProtocolDecl;
import org.scribble.type.kind.Global;
import org.scribble.type.name.GProtocolName;
import org.scribble.type.name.Role;

// Cf. STStateChanApiBuilder
public class ParamCoreSTSessionApiBuilder  // FIXME: make base STSessionApiBuilder
{
	//private ParamCoreSTStateChanApiBuilder api;
	private ParamCoreSTEndpointApiGenerator apigen;
	
	//public ParamCoreSTSessionApiBuilder(ParamCoreSTStateChanApiBuilder api)
	public ParamCoreSTSessionApiBuilder(ParamCoreSTEndpointApiGenerator apigen)
	{
		this.apigen = apigen;
	}

	//@Override
	public Map<String, String> build()  // FIXME: factor out
	{
		Module mod = this.apigen.job.getContext().getModule(this.apigen.proto.getPrefix());
		GProtocolName simpname = this.apigen.proto.getSimpleName();
		ProtocolDecl<Global> gpd = mod.getProtocolDecl(simpname);
		List<Role> roles = gpd.header.roledecls.getRoles();

		/*Set<EState> instates = new HashSet<>();
		Predicate<EState> f = s -> s.getStateKind() == EStateKind.UNARY_INPUT || s.getStateKind() == EStateKind.POLY_INPUT;
		if (f.test(this.apigen.graph.init))
		{
			instates.add(this.apigen.graph.init);
		}
		instates.addAll(MState.getReachableStates(this.apigen.graph.init).stream().filter(f).collect(Collectors.toSet()));*/

		// roles
		String sessPack =
					//"package " + this.apigen.getRootPackage() + "\n"  // FIXME: factor out
					this.apigen.generateRootPackageDecl() + "\n"
				+ "\n"
				//+ "import \"" + ParamCoreSTApiGenConstants.GO_SCRIBBLERUNTIME_PACKAGE + "\"\n"
				+ this.apigen.generateScribbleRuntimeImports() + "\n";

		sessPack += "\n"
				+ "type " + simpname + " struct {\n"
				+ roles.stream().map(r -> r + " " + ParamCoreSTApiGenConstants.GO_ROLE_TYPE + "\n").collect(Collectors.joining(""))
						// Just need role name constants for now -- params not fixed until endpoint creation
				+ "}\n"
				+ "\n" 
				+ "func New" + simpname + "() *" + simpname + " {\n"
				+ "return &" + simpname + "{ " + roles.stream().map(r -> ParamCoreSTApiGenConstants.GO_ROLE_CONSTRUCTOR
						+ "(\"" + r + "\")").collect(Collectors.joining(", ")) + " }\n"
						 // Singleton types?
				+ "}\n";

		/*sessPack +=
				roles.stream().map(r -> 
						  "type _" + r + " struct { }\n"
				  	+ "\n"
				  	+ "func (*_" + r +") GetRoleName() string {\n"
				  	+ "return \"" + r + "\"\n"
				  	+ "}\n"
				  	+ "\n"
				  	+ "var __" + r + " *_" + r + "\n"
				  	+ "\n"
				  	+ "func new" + r + "() *_" + r + " {\n"  // FIXME: not concurrent
				  	+ "if __" + r + " == nil {\n"
				  	+ "__"+ r + " = &_" + r + "{}\n"
				  	+ "}\n"
				  	+ "return __" + r + "\n"
				  	+ "}"
				  ).collect(Collectors.joining("\n\n")) + "\n"
				+ "\n";*/
		
		// Protocol and role specific endpoints
		//Function<Role, String> epTypeName = r -> "_Endpoint" + simpname + "_" + r;
		sessPack +=
				roles.stream().map(r ->
				{
					String epTypeName = ParamCoreSTEndpointApiGenerator.getGeneratedEndpointType(simpname, r);
					return
							  "\n\ntype " + epTypeName + " struct {\n"  // FIXME: factor out
							+ "proto *" + simpname + "\n"
							+ this.apigen.actuals.keySet().stream().filter(a -> a.getName().equals(r)).map(a -> 
							  {
									String actualName = ParamCoreSTEndpointApiGenerator.getGeneratedActualRoleName(a);
									return "sub_" + actualName + " func(*" + actualName + "_1) *"
											+ ParamCoreSTApiGenConstants.GO_SCHAN_END_TYPE + "\n";
							  }).collect(Collectors.joining(""))
							+ "params map[string]int\n"
							+ "}\n"
							+ "\n"
							+ "func (p *" + simpname + ") New" + epTypeName
									+ "(params map[string]int) (*" + epTypeName + ") {\n"
							+ "return &" + epTypeName + "{ p, params }\n"
							+ "}\n"
							+ "\n"
							+ this.apigen.actuals.keySet().stream().filter(a -> a.getName().equals(r)).map(a -> 
							  {
									String actualName = ParamCoreSTEndpointApiGenerator.getGeneratedActualRoleName(a);
							  	return 
										"\nfunc (r *" + epTypeName + ") "
												+ "Register_" + actualName
												+ "(impl func(*" + actualName + "_1) *" + ParamCoreSTApiGenConstants.GO_SCHAN_END_TYPE + ") {\n"
												+ "r.sub_" + actualName + " = impl\n"
												+ "}\n";
							  }).collect(Collectors.joining(""));
				}).collect(Collectors.joining(""));
		
		String dir = this.apigen.proto.toString().replaceAll("\\.", "/") + "/";
		Map<String, String> res = new HashMap<>();
		res.put(dir + simpname + ".go", sessPack);
		return res;
	}
}
