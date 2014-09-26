package net.sf.orcc.backends.llvm.assembly;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import net.sf.orcc.backends.AbstractBackend;
import net.sf.orcc.backends.llvm.aot.CMakePrinter;
import net.sf.orcc.backends.llvm.aot.InstancePrinter;
import net.sf.orcc.backends.llvm.aot.NetworkPrinter;
import net.sf.orcc.backends.llvm.transform.ListInitializer;
import net.sf.orcc.backends.llvm.transform.StringTransformation;
import net.sf.orcc.backends.llvm.transform.TemplateInfoComputing;
import net.sf.orcc.backends.transform.CastAdder;
import net.sf.orcc.backends.transform.DisconnectedOutputPortRemoval;
import net.sf.orcc.backends.transform.EmptyBlockRemover;
import net.sf.orcc.backends.transform.InstPhiTransformation;
import net.sf.orcc.backends.transform.Multi2MonoToken;
import net.sf.orcc.backends.transform.ShortCircuitTransformation;
import net.sf.orcc.backends.transform.ssa.ConstantPropagator;
import net.sf.orcc.backends.transform.ssa.CopyPropagator;
import net.sf.orcc.backends.util.Alignable;
import net.sf.orcc.df.Actor;
import net.sf.orcc.df.Instance;
import net.sf.orcc.df.Network;
import net.sf.orcc.df.transform.Instantiator;
import net.sf.orcc.df.transform.NetworkFlattener;
import net.sf.orcc.df.transform.TypeResizer;
import net.sf.orcc.df.transform.UnitImporter;
import net.sf.orcc.df.util.DfVisitor;
import net.sf.orcc.ir.CfgNode;
import net.sf.orcc.ir.Expression;
import net.sf.orcc.ir.transform.BlockCombine;
import net.sf.orcc.ir.transform.ControlFlowAnalyzer;
import net.sf.orcc.ir.transform.DeadCodeElimination;
import net.sf.orcc.ir.transform.DeadGlobalElimination;
import net.sf.orcc.ir.transform.DeadVariableRemoval;
import net.sf.orcc.ir.transform.RenameTransformation;
import net.sf.orcc.ir.transform.SSATransformation;
import net.sf.orcc.ir.transform.SSAVariableRenamer;
import net.sf.orcc.ir.transform.TacTransformation;
import net.sf.orcc.tools.classifier.Classifier;
import net.sf.orcc.tools.merger.action.ActionMerger;
import net.sf.orcc.tools.merger.actor.ActorMerger;
import net.sf.orcc.util.FilesManager;
import net.sf.orcc.util.OrccLogger;
import net.sf.orcc.util.Result;
import net.sf.orcc.util.Void;

/**
 * IPPRO back-end.
 * 
 * @author Burak Bardak
 * 
 */
public class AssemblyBackend extends AbstractBackend {


		/**
		 * Path to target "src" folder
		 */
		private String srcPath;

		private final NetworkPrinter netPrinter;
		private final CMakePrinter cmakePrinter;
		private final InstancePrinter childrenPrinter;

		// The map will also be used in TTABackend, that's why it is
		// declared as class member
		protected final Map<String, String> renameMap;

		public AssemblyBackend() {
			netPrinter = new NetworkPrinter();
			cmakePrinter = new CMakePrinter();
			childrenPrinter = new InstancePrinter();

			// Configure the map used in RenameTransformation
			renameMap = new HashMap<String, String>();
			renameMap.put("abs", "abs_");
			renameMap.put("getw", "getw_");
			renameMap.put("index", "index_");
			renameMap.put("min", "min_");
			renameMap.put("max", "max_");
			renameMap.put("select", "select_");
		}

		@Override
		protected void doInitializeOptions() {
			// Configure the options used in code generation
			netPrinter.setOptions(getOptions());
			childrenPrinter.setOptions(getOptions());

			// Create the empty folders
			new File(path, "bin").mkdir();
			new File(path, "build").mkdir();

			// Configure the path where source files will be written
			srcPath = new File(path, "src").toString();

			// -----------------------------------------------------
			// Transformations that will be applied on the Network
			// -----------------------------------------------------
			networkTransfos.add(new Instantiator(!debug));
			networkTransfos.add(new NetworkFlattener());
			networkTransfos.add(new UnitImporter());

			if (classify) {
				networkTransfos.add(new Classifier());
			}
			if (mergeActions) {
				networkTransfos.add(new ActionMerger());
			}
			if (mergeActors) {
				networkTransfos.add(new ActorMerger());
			}
			if (convertMulti2Mono) {
				networkTransfos.add(new Multi2MonoToken());
			}

			networkTransfos.add(new DisconnectedOutputPortRemoval());
			networkTransfos.add(new TypeResizer(true, false, false, false));
			networkTransfos.add(new StringTransformation());
			networkTransfos.add(new DfVisitor<Expression>(
					new ShortCircuitTransformation()));
			networkTransfos.add(new DfVisitor<Void>(new SSATransformation()));
			networkTransfos.add(new DeadGlobalElimination());
			networkTransfos.add(new DfVisitor<Void>(new DeadCodeElimination()));
			networkTransfos.add(new DfVisitor<Void>(new DeadVariableRemoval()));
			networkTransfos.add(new RenameTransformation(renameMap));
			networkTransfos.add(new DfVisitor<Expression>(new TacTransformation()));
			networkTransfos.add(new DfVisitor<Void>(new CopyPropagator()));
			networkTransfos.add(new DfVisitor<Void>(new ConstantPropagator()));
			networkTransfos.add(new DfVisitor<Void>(new InstPhiTransformation()));
			networkTransfos.add(new DfVisitor<Expression>(
					new CastAdder(false, true)));
			networkTransfos.add(new DfVisitor<Void>(new EmptyBlockRemover()));
			networkTransfos.add(new DfVisitor<Void>(new BlockCombine()));
			networkTransfos.add(new DfVisitor<CfgNode>(new ControlFlowAnalyzer()));
			networkTransfos.add(new DfVisitor<Void>(new ListInitializer()));

			// computes names of local variables
			networkTransfos.add(new DfVisitor<Void>(new SSAVariableRenamer()));
		}

		@Override
		protected void doValidate(Network network) {
			super.doValidate(network);

			new DfVisitor<Void>(new TemplateInfoComputing()).doSwitch(network);
			network.computeTemplateMaps();

			// update "vectorizable" information
			Alignable.setAlignability(network);
		}

		@Override
		protected Result doLibrariesExtraction() {
			Result result = FilesManager.extract("/runtime/C/README.txt", path);
			// Copy specific windows batch file
			if (FilesManager.getCurrentOS() == FilesManager.OS_WINDOWS) {
				result.merge(FilesManager.extract(
						"/runtime/C/run_cmake_with_VS_env.bat", path));
			}

			OrccLogger.traceln("Export libraries sources");
			result.merge(FilesManager.extract("/runtime/C/libs", path));

			return result;
		}

		@Override
		protected Result doGenerateNetwork(Network network) {
			// Configure the network
			netPrinter.setNetwork(network);
			// Write the file
			return FilesManager.writeFile(netPrinter.getNetworkFileContent(),
					srcPath, network.getSimpleName() + ".IPPRO");
		}

		@Override
		protected Result doAdditionalGeneration(Network network) {

			cmakePrinter.setNetwork(network);

			final Result result = Result.newInstance();
			result.merge(FilesManager.writeFile(cmakePrinter.rootCMakeContent(),
					path, "CMakeLists.txt"));
			result.merge(FilesManager.writeFile(cmakePrinter.srcCMakeContent(),
					srcPath, "CMakeLists.txt"));

			return result;
		}

		@Override
		protected Result doGenerateInstance(Instance instance) {
			childrenPrinter.setInstance(instance);
			return FilesManager.writeFile(childrenPrinter.getContent(), srcPath,
					instance.getName() + ".IPPRO");
		}

		@Override
		protected Result doGenerateActor(Actor actor) {
			childrenPrinter.setActor(actor);
			return FilesManager.writeFile(childrenPrinter.getContent(), srcPath,
					actor.getName() + ".IPPRO");
		}
	}

