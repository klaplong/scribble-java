package org.scribble.codegen.java.endpointapi.ioifaces;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.scribble.codegen.java.endpointapi.ApiGenerator;
import org.scribble.codegen.java.endpointapi.CaseSocketGenerator;
import org.scribble.codegen.java.endpointapi.HandlerInterfaceGenerator;
import org.scribble.codegen.java.endpointapi.ScribSocketGenerator;
import org.scribble.codegen.java.endpointapi.SessionApiGenerator;
import org.scribble.codegen.java.endpointapi.StateChannelApiGenerator;
import org.scribble.codegen.java.util.InterfaceBuilder;
import org.scribble.codegen.java.util.JavaBuilder;
import org.scribble.codegen.java.util.MethodBuilder;
import org.scribble.codegen.java.util.TypeBuilder;
import org.scribble.model.local.EndpointState;
import org.scribble.model.local.EndpointState.Kind;
import org.scribble.model.local.IOAction;
import org.scribble.sesstype.name.GProtocolName;
import org.scribble.sesstype.name.Role;

// Cf. StateChannelApiGenerator
public class IOInterfacesGenerator extends ApiGenerator
{
	protected final StateChannelApiGenerator apigen;

	private final Map<IOAction, InterfaceBuilder> actions = new HashMap<>();
	private final Map<IOAction, InterfaceBuilder> succs = new HashMap<>();
	private final Map<String, InterfaceBuilder> iostates = new HashMap<>();  // Key is interface simple name
	
	private final Map<EndpointState, Set<IOAction>> preActions = new HashMap<>();  // Pre set: the actions that lead to each state
	private final Map<EndpointState, Set<InterfaceBuilder>> preds = new HashMap<>();
	
	private final Map<EndpointState, Set<IOAction>> branchPostActions = new HashMap<>();
	//private final Map<EndpointState, Set<InterfaceBuilder>> branchSuccs = new HashMap<>();
	private final Map<String, List<IOAction>> branchSuccs = new HashMap<>();  // key: HandleInterface name  // Sorted when collected

	public IOInterfacesGenerator(StateChannelApiGenerator apigen)
	{
		super(apigen.getJob(), apigen.getGProtocolName());
		this.apigen = apigen;

		GProtocolName fullname = apigen.getGProtocolName();
		Role self = getSelf();
		EndpointState init = this.job.getContext().getEndpointGraph(fullname, self).init;

		generateActionAndSuccessorInterfacesAndCollectPreActions(new HashSet<>(), init);
		generateIOStateInterfacesFirstPass(new HashSet<>(), init);
		collectPreds();
		generateIOStateInterfacesSecondPass(new HashSet<>(), init);
		collectBranchSuccs();
		generateHandleInterfaces(new HashSet<>(), init);
		generateHandleInterfacesSecondPass(new HashSet<>(), init);
		addIOStateInterfacesToStateChannels(new HashSet<>(), init);  // Except EndSocket

		// Successor I/f's for EndSocket
		EndpointState term = EndpointState.findTerminalState(new HashSet<>(), init);
		if (term != null)
		{
			TypeBuilder tb = this.apigen.getType(ScribSocketGenerator.GENERATED_ENDSOCKET_NAME);
			tb.addImports(getIOInterfacePackageName(this.gpn, self) + ".*");
			for (InterfaceBuilder ib : this.preds.get(term))
			{
				tb.addInterfaces(ib.getName());
			}
		}
	}

	@Override
	public Map<String, String> generateApi()
	{
		Map<String, String> output = new HashMap<>();
		String prefix = getIOInterfacePackageName(this.gpn, getSelf()).replace('.', '/') + "/";
		this.actions.values().stream().forEach((ib) -> output.put(prefix + ib.getName() + ".java", ib.build()));
		this.succs.values().stream().forEach((ib) -> output.put(prefix + ib.getName() + ".java", ib.build()));
		this.iostates.values().stream().forEach((tb) -> output.put(prefix + tb.getName() + ".java", tb.build()));
		return output;
	}
	
	// Factor out FSM visitor?
	private void generateActionAndSuccessorInterfacesAndCollectPreActions(Set<EndpointState> visited, EndpointState s)
	{
		if (visited.contains(s) || s.isTerminal())
		{
			return;
		}
		visited.add(s);

		for (IOAction a : s.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
		{
			if (!this.actions.containsKey(a))
			{
				this.actions.put(a, new ActionInterfaceGenerator(this.apigen, s, a).generateType());
				this.succs.put(a, new SuccessorInterfaceGenerator(this.apigen, s, a).generateType());
			}
			
			EndpointState succ = s.accept(a);
			putPreAction(succ, a);

			if (s.getStateKind() == Kind.POLY_INPUT)
			{
				/*for (IOAction b : s.accept(a).getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
				{
					putBranchPostAction(s, b);
				}*/
				putBranchPostAction(s, a);
			}

			generateActionAndSuccessorInterfacesAndCollectPreActions(visited, succ);
			/*Set<EndpointState> tmp = new HashSet<>(visited);
			tmp.add(s);  // merge paths visited multiple times
			generateActionAndSuccessorInterfacesAndCollectPredecessors(tmp, succ);*/
		}
	}

	// Generates partial IO State Interfaces
	private void generateIOStateInterfacesFirstPass(Set<EndpointState> visited, EndpointState s)
	{
		if (visited.contains(s) || s.isTerminal())
		{
			return;
		}
		
		String key = IOStateInterfaceGenerator.getIOStateInterfaceName(getSelf(), s);
		if (!this.iostates.containsKey(key))  // Don't generate if one already exists (up to this pass, repeats will all be the same, i.e. name, Action Interfaces, and action-succ parameters)
		{
			// Make the partial I/O State Interface (Successor Interfaces and cast methods added later -- different states may share same State I/f)
			IOStateInterfaceGenerator ifgen = null;
			switch (s.getStateKind())
			{
				case OUTPUT:
					ifgen = new SelectInterfaceGenerator(this.apigen, this.actions, s);
					break;
				case UNARY_INPUT:
					ifgen = new ReceiveInterfaceGenerator(this.apigen, this.actions, s);
					break;
				case POLY_INPUT:
					InterfaceBuilder cases = new CaseInterfaceGenerator(this.apigen, this.actions, s).generateType();
					this.iostates.put(cases.getName(), cases);
					ifgen = new BranchInterfaceGenerator(this.apigen, this.actions, s);
					break;
				case TERMINAL:
				default:
					throw new RuntimeException("TODO:");
			}
			this.iostates.put(key, ifgen.generateType());
		}
		
		visited.add(s);
		for (IOAction a : s.getAcceptable())
		{
			generateIOStateInterfacesFirstPass(visited, s.accept(a));
		}
	}

	// Adds Successor Interfaces and to-cast methods to IO State Interfaces
	private void generateIOStateInterfacesSecondPass(Set<EndpointState> visited, EndpointState s)
	{
		if (visited.contains(s) || s.isTerminal())
		{
			return;
		}

		Set<InterfaceBuilder> succifs = this.preds.get(s);  // Successor interfaces to be implemented by IO State Interface of s
		if (succifs != null)
		{
			InterfaceBuilder iostate = this.iostates.get(IOStateInterfaceGenerator.getIOStateInterfaceName(getSelf(), s));
			for (InterfaceBuilder pred : succifs)  // pred is a Successor Interface for the state s 
			{
				// May already have "visited" this State I/f for a different state -- Interfaces recorded as a Set, to support repeated adds
				iostate.addInterfaces(pred.getName());  // Adds Successor Interfaces to this I/O State Interface
				String ret = iostate.getName() + "<"
						+ IntStream.range(0, iostate.getParameters().size()).mapToObj((i) -> "?").collect(Collectors.joining(", ")) + ">";
				addToCastMethod(pred, ret);
				
				for (MethodBuilder cast : pred.getDefaultMethods())  // cast is a default method (a to cast -- hacky) in pred
				{
					// Overriding every Successor I/f to methods in the I/O State I/f, even if unnecessary
					MethodBuilder mb = addToCastMethod(iostate, cast.getReturn());
					if (mb != null)
					{
						mb.addAnnotations("@Override");
					}
				}
			}
		}
		
		visited.add(s);
		for (IOAction a : s.getAcceptable())
		{
			generateIOStateInterfacesSecondPass(visited, s.accept(a));
		}
	}

	private void generateHandleInterfaces(Set<EndpointState> visited, EndpointState s)
	{
		if (visited.contains(s) || s.isTerminal())
		{
			return;
		}

		if (s.getStateKind() == Kind.POLY_INPUT)
		{
			Set<InterfaceBuilder> succifs = this.preds.get(s);
			String key = HandleInterfaceGenerator.getHandleInterfaceName(getSelf(), s);
			if (!this.iostates.containsKey(key))  // Don't generate if one already exists (up to this pass, repeats will all be the same, i.e. name, Action Interfaces, and action-succ parameters)
			{
				// Make the partial I/O State Interface (Successor Interfaces and cast methods added later -- different states may share same State I/f)
				IOStateInterfaceGenerator ifgen = new HandleInterfaceGenerator(this, this.actions, s, succifs);
				this.iostates.put(key, ifgen.generateType());
			}
		}
		
		visited.add(s);
		for (IOAction a : s.getAcceptable())
		{
			generateHandleInterfaces(visited, s.accept(a));
		}
	}

	private void generateHandleInterfacesSecondPass(Set<EndpointState> visited, EndpointState s)
	{
		if (visited.contains(s) || s.isTerminal())
		{
			return;
		}

		if (s.getStateKind() == Kind.POLY_INPUT)
		{
			GProtocolName gpn = this.apigen.getGProtocolName();
			Role self = this.apigen.getSelf();

			//String foo = HandlerInterfaceGenerator.getHandlerInterfaceName(IOStateInterfaceGenerator.getIOStateInterfaceName(self, s)); 
			String key = HandleInterfaceGenerator.getHandleInterfaceName(self, s);
			List<IOAction> succifs = this.branchSuccs.get(key);
			if (succifs != null)
			{
				//InterfaceBuilder handleif = this.iostates.get(HandleInterfaceGenerator.getHandleInterfaceName(self, s));
				InterfaceBuilder handleif = this.iostates.get(key);
				
				System.out.println("AAA: " + handleif.getName() + ", " + handleif.getParameters().isEmpty());
				
				if (handleif.getParameters().isEmpty())  // Hacky?
				{
					int i = 1;
					for (IOAction b : succifs)  // Already sorted
					{
						handleif.addParameters("__Succ" + i + " extends " + SuccessorInterfaceGenerator.getSuccessorInterfaceName(b));//this.succs.get(b).getName());
						i++;
					}

					handleif.addImports(SessionApiGenerator.getOpsPackageName(gpn) + ".*");
					//int j = 1; 
					/*Iterator<IOAction> foo = s.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).iterator();
					EndpointState succ = s.accept(foo.next());*/
				}

				//Map<IOAction, Integer> count = new HashMap<>();
				List<IOAction> tmp = this.branchSuccs.get(key);
				//tmp.stream().forEach((a) -> count.put(a, (int) tmp.stream().filter((b) -> b.equals(a)).count()));
				Map<IOAction, Integer> count = new HashMap<>();
				for (IOAction a : this.branchPostActions.get(s).stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
				{
				/*for (IOAction b : succifs)
				{
					if (!succ.isAcceptable(b))
					{
						succ = s.accept(foo.next());
					}*/
					EndpointState succ = s.accept(a);
					MethodBuilder mb = handleif.newAbstractMethod();
					HandlerInterfaceGenerator.setHandleMethodHeaderWithoutParamTypes(this.apigen, mb);
					//j = HandleInterfaceGenerator.setHandleMethodSuccessorParam(this, self, succ, mb, j);
					HandleInterfaceGenerator.setHandleMethodSuccessorParam(this, self, succ, mb, tmp, count);
					/*for (IOAction b : count.keySet())
					{
						for (int j = 0; j < count.get(b); j++)
						{
							tmp.remove(b);
						}
					}*/
					HandlerInterfaceGenerator.addHandleMethodOpAndPayloadParams(this.apigen, a, mb);
					
					handleif.checkDuplicateMethods(mb);  // Hacky
				//}
				}
			}
		}
				
		visited.add(s);
		for (IOAction a : s.getAcceptable())
		{
			generateHandleInterfacesSecondPass(visited, s.accept(a));
		}
	}
	
	// Except EndSocket
	private void addIOStateInterfacesToStateChannels(Set<EndpointState> visited, EndpointState s)
	{
		if (visited.contains(s) || s.isTerminal())
		{
			return;
		}

		Role self = getSelf();
		String scname = this.apigen.getSocketClassName(s);
		String ioname = IOStateInterfaceGenerator.getIOStateInterfaceName(self, s);
		TypeBuilder tb = this.apigen.getType(scname);
		
		// Add I/O State Interface to each ScribSocket (except CaseSocket)
		// Do here (not inside I/O State Interface generators) because multiple states can share the same I/O State Interface
		tb.addImports(getIOInterfacePackageName(this.gpn, self) + ".*");
		tb.addInterfaces(ioname + getConcreteSuccessorParameters(s));
		
		InterfaceBuilder iostate = this.iostates.get(ioname);
		MethodBuilder mb = addToCastMethod(iostate, scname);
		if (mb != null)
		{
			iostate.addImports(SessionApiGenerator.getStateChannelPackageName(this.gpn, self) + ".*");
		}

		if (s.getStateKind() == Kind.POLY_INPUT)
		{
			// Add CaseInterface to each CaseSocket
			TypeBuilder cases = this.apigen.getType(CaseSocketGenerator.getCaseSocketName(this.apigen.getSocketClassName(s)));
			cases.addImports(getIOInterfacePackageName(this.gpn, self) + ".*");
			cases.addInterfaces(CaseInterfaceGenerator.getCasesInterfaceName(self, s) + getConcreteSuccessorParameters(s));
			
			// Add HandleInterface to each HandlerInterface
			InterfaceBuilder handler = (InterfaceBuilder) this.apigen.getType(HandlerInterfaceGenerator.getHandlerInterfaceName(this.apigen.getSocketClassName(s)));
			handler.addImports(getIOInterfacePackageName(this.gpn, self) + ".*");
			// FIXME: factor out with HandleInterfaceGenerator and getConcreteSuccessorParameters
			String tmp = "";
			boolean first = true;
			/*for (IOAction a : s.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
			{
				EndpointState succ = s.accept(a);
				for (IOAction b : succ.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
				{
					if (first)
					{
						first = false;
					}
					else
					{
						tmp += ", ";
					}
					tmp += this.getSuccName.apply(succ.accept(b));
				}
			}*/
			String handle = HandleInterfaceGenerator.getHandleInterfaceName(self, s);
			List<IOAction> foo1 = new LinkedList<>();
			List<EndpointState> bar1 = new LinkedList<>();
			for (IOAction a : s.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
			{
				EndpointState succ = s.accept(a);
				for (IOAction b : succ.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
				{
					foo1.add(b);
					bar1.add(succ);
				}
			}
			System.out.println("BBB: " + handle);
			for (IOAction a : this.branchSuccs.get(handle))
			{
				if (first)
				{
					first = false;
				}
				else
				{
					tmp += ", ";
				}
				if (foo1.contains(a))
				{
					EndpointState succ = bar1.get(foo1.indexOf(a));
					tmp += this.getSuccName.apply(succ.accept(a));
					foo1.remove(a);
					bar1.remove(succ);
				}
				else
				{
					tmp += SuccessorInterfaceGenerator.getSuccessorInterfaceName(a);
				}
			}	
			
			handler.addInterfaces(handle + "<" + tmp + ">");
			
			// Override abstract handle methods with default cast implementation
			for (IOAction a : s.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
			{
				EndpointState succ = s.accept(a);
				this.iostates.get(HandleInterfaceGenerator.getHandleInterfaceName(self, succ));
				MethodBuilder override = handler.newDefaultMethod();
				//override.addModifiers(JavaBuilder.FINAL);  // Default methods cannot be final
				HandlerInterfaceGenerator.setHandleMethodHeaderWithoutParamTypes(this.apigen, override);
				//HandleInterfaceGenerator.setHandleMethodSuccessorParam(this, self, succ, override);
				// FIXME: factor out with HandleInterfaceGenerator.setHandleMethodSuccessorParam
				String nextClass = this.apigen.getSocketClassName(succ);
				if (succ.isTerminal())
				{
					override.addParameters(ScribSocketGenerator.ENDSOCKET_CLASS + "<?, ?> end");
				}
				else
				{
					InterfaceBuilder next = getIOStateInterface(IOStateInterfaceGenerator.getIOStateInterfaceName(self, succ));  // Select/Receive/Branch
					String ret = next.getName() + "<";
					//ret += "<" + next.getParameters().stream().map((p) -> "__Succ" + i).collect(Collectors.joining(", ")) + ">";  // FIXME: fragile?
					boolean bar = true;
					for (IOAction b : succ.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))  // FIXME: factor out with getHandleInterfaceIOActionParams
					{
						if (bar)
						{
							bar = false;
						}
						else
						{
							ret += ", ";
						}
						EndpointState foo = succ.accept(b);
						if (foo.isTerminal())
						{
							ret += ScribSocketGenerator.GENERATED_ENDSOCKET_NAME;
						}
						else
						{
							ret += this.apigen.getSocketClassName(foo);
						}
					}
					ret += ">";
					override.addParameters(ret + " schan");
				}
				HandlerInterfaceGenerator.addHandleMethodOpAndPayloadParams(this.apigen, a, override);
				// FIXME: factor out
				String ln = "receive((";
				if (succ.isTerminal())  // factor out
				{
					ln += "EndSocket) end";
				}
				else
				{
					ln += nextClass + ") schan";
				}
				ln += ", op";
				String args;
				if (a.mid.isOp())  // factor out
				{
					args = IntStream.rangeClosed(1, a.payload.elems.size()).mapToObj((i) -> "arg" + i).collect(Collectors.joining(", "));
					if (!args.equals(""))
					{
						args = ", " + args;
					}
				}
				else
				{
					args = ", arg";
				}
				ln += args + ");";
				override.addBodyLine(ln);
				override.addAnnotations("@Override");
			}
		}
		
		visited.add(s);
		for (IOAction a : s.getAcceptable())
		{
			addIOStateInterfacesToStateChannels(visited, s.accept(a));
		}
	}
	
	// Pre: ib is a Successor I/f for the cast IO State I/f
	// Returns MethodBuilder, or null if none built
	private static MethodBuilder addToCastMethod(InterfaceBuilder ib, String ret)
	{
		if (ib.getDefaultMethods().stream().filter((def) -> def.getReturn().equals(ret)).count() > 0)
		{
			// Merge states entered from multiple paths, don't want to add cast multiple times -- still true for this case?
			// But duplicate cast check cast still needed anyway?
			return null;
		}
		MethodBuilder mb = ib.newDefaultMethod("to");
		mb.setReturn(ret);
		mb.addParameters(ret + " cast");
		mb.addBodyLine(JavaBuilder.RETURN + " (" + ret + ") this;");
		return mb;
	}

	private final
		Function<EndpointState, String> getSuccName = (succ) ->
				(succ.isTerminal())
						? ScribSocketGenerator.GENERATED_ENDSOCKET_NAME
						: this.apigen.getSocketClassName(succ);

	private String getConcreteSuccessorParameters(EndpointState s)
	{
		return "<" +
				s.getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR)
						.map((a) -> this.getSuccName.apply(s.accept(a))).collect(Collectors.joining(", "))
				+ ">";
	}
	
	private void putPreAction(EndpointState s, IOAction a)
	{
		putMapSet(this.preActions, s, a);
	}

	private void putBranchPostAction(EndpointState s, IOAction a)
	{
		putMapSet(this.branchPostActions, s, a);
	}

	private static <K, V> void putMapSet(Map<K, Set<V>> map, K k, V v)
	{
		Set<V> tmp = map.get(k);
		if (tmp == null)
		{
			tmp = new LinkedHashSet<>();
			map.put(k, tmp);
		}
		tmp.add(v);
	}
	
	// Successor I/f's to be implemented by each I/O State I/f
	private void collectPreds()
	{
		for (EndpointState s : this.preActions.keySet())
		{
			Set<InterfaceBuilder> tmp = new HashSet<>();
			for (IOAction a : this.preActions.get(s))  // sort?
			{
				tmp.add(this.succs.get(a));
			}
			this.preds.put(s, tmp);
		}
	}
	
	private void collectBranchSuccs()
	{
		Role self = getSelf();
		for (EndpointState s : this.branchPostActions.keySet())
		{
			//String key = HandlerInterfaceGenerator.getHandlerInterfaceName(IOStateInterfaceGenerator.getIOStateInterfaceName(self, s));
			String key = HandleInterfaceGenerator.getHandleInterfaceName(self, s);  // HandleInterface name

			List<IOAction> curr1 = new LinkedList<>();
			this.branchPostActions.get(s).forEach((a) -> curr1.addAll(s.accept(a).getAcceptable()));  // TODO: flatmap
			//List<IOAction> curr2 = curr1.stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList());
			
			List<IOAction> tmp = this.branchSuccs.get(key);
			if (tmp == null)
			{
				tmp = new LinkedList<>();
				//this.branchSuccs.put(key, tmp);
				tmp.addAll(curr1);
			}
			else
			{
				for (IOAction a : curr1)
				{
					long n = curr1.stream().filter((x) -> x.equals(a)).count();
					long m = tmp.stream().filter((x) -> x.equals(a)).count();
					System.out.println("EEE: " + curr1 + ",,, " + tmp);
					if (n > m)
					{
						for (int i = 0; i < n-m; i++)
						{
							tmp.add(a);
						}
					}
				}
			}
				
			this.branchSuccs.put(key, tmp.stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()));
			//System.out.println("AAA: " + this.branchSuccs.get(key));

			/*List<IOAction> tmp = this.branchSuccs.get(key);
			if (tmp == null)
			{
				tmp = new LinkedList<>();
				this.branchSuccs.put(key, tmp);
			}
			//this.branchPostActions.get(s).stream()//.sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR)
					//.forEach((a) -> { tmp.add(this.succs.get(a)); });
			for (IOAction a : this.branchPostActions.get(s))  // Already sorted -- guaranteed pairwise distinct (branch actions)  //.sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR)
			{
				// Not necessarily distinct (actions of the branch successor state)
				for (IOAction b : s.accept(a).getAcceptable().stream().sorted(IOStateInterfaceGenerator.IOACTION_COMPARATOR).collect(Collectors.toList()))
				{
					//tmp.add(this.succs.get(b));
					tmp.add(b);
				}
			}
			tmp = tmp.stream().so*/
		}
	}
	
	protected Role getSelf()
	{
		return this.apigen.getSelf();
	}

	protected static String getIOInterfacePackageName(GProtocolName gpn, Role self)
	{
		return SessionApiGenerator.getStateChannelPackageName(gpn, self) + ".ioifaces";
	}
	
	protected InterfaceBuilder getIOStateInterface(String name)
	{
		return this.iostates.get(name);
	}
}
