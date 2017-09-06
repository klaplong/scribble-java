package org.scribble.ext.go.core.codegen.statetype;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.scribble.ext.go.core.type.ParamActualRole;
import org.scribble.main.Job;
import org.scribble.main.ScribbleException;
import org.scribble.model.endpoint.EGraph;
import org.scribble.type.name.GProtocolName;
import org.scribble.type.name.Role;

// Duplicated from org.scribble.ext.go.codegen.statetype.go.GoSTEndpointApiGenerator
public class ParamCoreSTEndpointApiGenerator
{
	public final Job job;
	public final GProtocolName proto;
	public final Role self;  // FIXME: base endpoint API gen is role-oriented, while session API generator should be neutral
	public final Map<ParamActualRole, EGraph> actuals;
	//public final EGraph graph;
	
	public ParamCoreSTEndpointApiGenerator(Job job, GProtocolName fullname, Role self, Map<ParamActualRole, EGraph> actuals)
	{
		this.job = job;
		this.proto = fullname;
		this.self = self;
		this.actuals = Collections.unmodifiableMap(actuals);
		//this.graph = graph;
	}

	// N.B. the base EGraph class will probably be replaced by a more specific (and more helpful) param-core class later
	public Map<String, String> build() throws ScribbleException
	{
		Map<String, String> res = new HashMap<>();  // filepath -> source 
		res.putAll(buildSessionApi()); 
		for (Entry<ParamActualRole, EGraph> actual : this.actuals.entrySet())
		{
			res.putAll(buildStateChannelApi(actual.getKey(), actual.getValue()));
		}
		return res;
	}

	//@Override
	public Map<String, String> buildSessionApi()  // FIXME: factor out
	{
		this.job.debugPrintln("\n[param-core] Running " + ParamCoreSTSessionApiBuilder.class + " for " + this.proto + "@" + this.self);
		//throw new RuntimeException("[param-core] TODO:");
		return new ParamCoreSTSessionApiBuilder(this).build();
	}
	
	public Map<String, String> buildStateChannelApi(ParamActualRole actual, EGraph graph)  // FIXME: factor out
	{
		this.job.debugPrintln("\n[param-core] Running " + ParamCoreSTStateChanApiBuilder.class + " for " + this.proto + "@" + this.self);
		return new ParamCoreSTStateChanApiBuilder(this, actual, graph).build();
	}
	
	public String getGeneratedEndpointType()
	{
		/*return "Endpoint_" + this.proto.getSimpleName() + "_"
				//+ getGeneratedActualRoleName();  // No: endpoint covers all actual roles of this role name
				+ this.self;*/
		return getGeneratedEndpointType(this.proto.getSimpleName(), this.self);
	}

	public static String getGeneratedEndpointType(GProtocolName simpname, Role r)
	{
		//return "Endpoint_" + simpname + "_" + r;
		return simpname + "_" + r;
	}
	
	public static String getGeneratedActualRoleName(ParamActualRole actual)
	{
		return actual.getName()
				+ actual.ranges.toString().replaceAll("\\[", "_").replaceAll("\\]", "_").replaceAll("\\.", "_");
	}

	//@Override
	public String getRootPackage()  // Derives only from proto name
	{
		//throw new RuntimeException("[param-core] TODO:");
		return this.proto.getSimpleName().toString();
	}

	public String generateRootPackageDecl()
	{
		//throw new RuntimeException("[param-core] TODO: ");
		return "package " + getRootPackage();
	}

	//@Override
	public List<String> getScribbleRuntimeImports()  // FIXME: factor up
	{
		return Stream.of(
					ParamCoreSTApiGenConstants.GO_SCRIBBLERUNTIME_SESSION_PACKAGE,
					ParamCoreSTApiGenConstants.GO_SCRIBBLERUNTIME_SESSIONPARAM_PACKAGE
					//ParamCoreSTApiGenConstants.GO_SCRIBBLERUNTIME_TRANSPORT_PACKAGE
				).collect(Collectors.toList());
	}

	public String generateScribbleRuntimeImports()
	{
		return getScribbleRuntimeImports().stream().map(x -> "import \"" + x + "\"").collect(Collectors.joining("\n"));
	}
}
