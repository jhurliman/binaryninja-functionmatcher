#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/breadth_first_search.hpp>
#include <limits>
#include <queue>
#include "binaryninjaapi.h"

#define SQLITE_ENABLE_RTREE 1
#include "sqlite/sqlite3.h"
#include "sqlite/database.hpp"

using std::make_pair;
using std::map;
using std::pair;
using std::priority_queue;
using std::string;
using std::stringstream;
using std::vector;
namespace BN = BinaryNinja;

struct BasicBlockGraphProperties;

using BasicBlockGraph = boost::adjacency_list<
  boost::vecS,
  boost::vecS,
  boost::bidirectionalS,
  BN::Ref<BN::BasicBlock>,
  BN::BasicBlockEdge,
  BasicBlockGraphProperties
>;
using BasicBlockVertexID = boost::graph_traits<BasicBlockGraph>::vertex_descriptor;
using BasicBlockEdgeID = boost::graph_traits<BasicBlockGraph>::edge_descriptor;
using BasicBlockVertexSize = boost::graph_traits<BasicBlockGraph>::vertices_size_type;
using BasicBlockDistanceMap = map<BasicBlockVertexID, BasicBlockVertexSize>;

struct BasicBlockGraphProperties {
  map<uint64_t, BasicBlockVertexID> addressMap;
};

sqlite::database initDB(string filename);
void saveFunction(BN::BinaryView* bv, BN::Ref<BN::Function> func, sqlite::database& db);
vector<string> split(const string& s, char delim);

////////////////////////////////////////////////////////////////////////////////

static int64_t PRIMES[] = {
  3,
  5,
  7,
  11,
  13,
  17,
  19,
  23,
  29,
  31,
  37,
  41,
  43,
  47,
  53,
  59,
  61,
  67,
  71,
  73,
  79,
  83,
  89,
  97,
  101,
  103,
  107,
  109,
  113,
  127,
  131,
  137,
  139,
  149,
  151,
  157,
  163,
  173,
  179,
  181,
  191,
  193,
  197,
  199,
  211,
  223,
  227,
  229,
  233,
  239,
  241,
  251,
  257,
  263,
  269,
  271,
  277,
  281,
  283,
  293,
  307,
  311,
  313,
  317,
  331,
  337,
  347,
};

////////////////////////////////////////////////////////////////////////////////

void saveDatabase(BN::BinaryView* bv)
{
  BN::Ref<BN::Architecture> arch = bv->GetDefaultArchitecture();
  string archName = arch->GetName();
  
  string defaultName = split(bv->GetFile()->GetFilename(), '.').front() + ".bnsm";
  string filename;
  BinaryNinja::GetSaveFileNameInput(filename, "Save function database", "*.bnsm", defaultName);
  
  sqlite::database db = initDB(filename);
  
  for (auto&& func : bv->GetAnalysisFunctionList()) {
    saveFunction(bv, func, db);
  }
}

sqlite::database initDB(string filename) {
  sqlite::database db(filename, sqlite::read_write_create);
  
  db.execute("CREATE TABLE symbols("
               "id INTEGER PRIMARY KEY ASC,"
               "address BIGINT,"
               "full_name TEXT,"
               "short_name TEXT,"
               "raw_name TEXT"
             ")");
  
  db.execute("CREATE TABLE functions("
               "id INTEGER PRIMARY KEY ASC,"
               "address BIGINT,"
               "length INTEGER,"
               "spp BIGINT,"
               "indegree INTEGER,"
               "outdegree INTEGER,"
               "is_recursive TINYINT,"
               "basic_block_count INTEGER,"
               "edge_count INTEGER"
             ")");
  
  db.execute("CREATE TABLE basic_blocks("
               "id INTEGER PRIMARY KEY ASC,"
               "function_id INTEGER,"
               "address BIGINT,"
               "length INTEGER,"
               "spp BIGINT,"
               "indegree INTEGER,"
               "outdegree INTEGER,"
               "is_recursive TINYINT,"
               "distance_to_entry INTEGER,"
               "distance_to_exit INTEGER,"
               "call_count INTEGER"
             ")");
  
  db.execute("CREATE TABLE function_string_refs("
               "function_id INTEGER,"
               "string_hash INTEGER"
             ")");
  
  db.execute("CREATE TABLE basic_block_string_refs("
               "basic_block_id INTEGER,"
               "string_hash INTEGER"
             ")");
  
  return db;
}

//template<class It>
//boost::iterator_range<It> pair_range(std::pair<It, It> const& p) {
//  return boost::make_iterator_range(p.first, p.second);
//}

void buildBasicBlockGraph(const BN::Ref<BN::Function> func, BasicBlockGraph& g) {
  const auto blocks = func->GetBasicBlocks();
  
  auto&& addressMap = g[boost::graph_bundle].addressMap;
  
  // Create vertices from all of the basic blocks in this function
  for (auto&& block : blocks) {
    BasicBlockVertexID id = boost::add_vertex(g);
    g[id] = block;
    addressMap[block->GetStart()] = id;
  }
  
  // Create edges between the basic blocks
  for (auto&& block : blocks) {
    const auto edges = block->GetOutgoingEdges();
    const BasicBlockVertexID a = addressMap.at(block->GetStart());
    
    for (auto&& edge : edges) {
      const auto bI = addressMap.find(edge.target);
      if (bI != addressMap.end()) {
        const BasicBlockVertexID b = bI->second;
        const BasicBlockEdgeID id = boost::add_edge(a, b, g).first;
        g[id] = edge;
      }
    }
  }
}

void buildDistanceMap(const BasicBlockGraph& g, BasicBlockVertexID start, BasicBlockDistanceMap& distances) {
  using ColorMap = map<BasicBlockVertexID, boost::default_color_type>;
  
  ColorMap colorMap;
  boost::queue<BasicBlockVertexID> queue;
  
  boost::breadth_first_visit(g, start, queue,
    boost::make_bfs_visitor(
      boost::record_distances(
        boost::associative_property_map<BasicBlockDistanceMap>(distances), boost::on_tree_edge()
      )
    ),
    boost::associative_property_map<ColorMap>(colorMap)
  );
}

void saveFunction(BN::BinaryView* bv, BN::Ref<BN::Function> func, sqlite::database& db) {
  BN::Ref<BN::Architecture> arch = bv->GetDefaultArchitecture();
  vector<BN::Ref<BN::BasicBlock>> basicBlocks = func->GetBasicBlocks();
  BN::Ref<BN::LowLevelILFunction> llil = func->GetLowLevelIL();
  size_t count = llil->GetInstructionCount();
  
  BasicBlockGraph g;
  buildBasicBlockGraph(func, g);
  auto&& addressMap = g[boost::graph_bundle].addressMap;
  
  int64_t address = static_cast<int64_t>(func->GetStart());
  int32_t length = 0;
  int64_t spp = 1;
  size_t indegree = bv->GetCodeReferences(address).size();
  size_t outdegree = 0;
  bool isRecursive = false;
  size_t basicBlockCount = basicBlocks.size();
  size_t edgeCount = boost::num_edges(g);
  
  for (auto&& block : basicBlocks) {
    edgeCount += block->GetOutgoingEdges().size();
    length += static_cast<int32_t>(block->GetLength());
  }
  
  for (size_t i = 0; i < count; i++) {
    BNLowLevelILInstruction il = llil->operator[](i);
    
    spp *= PRIMES[il.operation];
    
    switch (il.operation) {
      case LLIL_CALL:
        ++outdegree;
        if (il.sourceOperand == address) { isRecursive = true; }
        break;
      case LLIL_SYSCALL:
        ++outdegree;
        break;
      default:
        break;
    }
  }
  
  sqlite::statement stmt(db.prepare_statement(
    "INSERT INTO functions "
    "(address, length, spp, indegree, outdegree, is_recursive, basic_block_count, edge_count) "
    "VALUES (:address, :length, :spp, :indegree, :outdegree, :is_recursive, :basic_block_count, :edge_count)"
  ));
  stmt.bind(":address", address);
  stmt.bind(":length", length);
  stmt.bind(":spp", spp);
  stmt.bind(":indegree", indegree);
  stmt.bind(":outdegree", outdegree);
  stmt.bind(":is_recursive", isRecursive);
  stmt.bind(":basic_block_count", basicBlockCount);
  stmt.bind(":edge_count", edgeCount);
  
  sqlite::result results(db.execute(stmt));
  int64_t functionID = sqlite3_last_insert_rowid(db.getDB());
  
  BasicBlockVertexID entryID = addressMap.at(func->GetStart());
  
  BasicBlockDistanceMap entryDistances;
  entryDistances[entryID] = 0;
  buildDistanceMap(g, entryID, entryDistances);
  
  for (auto&& block : basicBlocks) {
    BasicBlockVertexID v = addressMap.at(block->GetStart());
    
    address = static_cast<int64_t>(block->GetStart());
    length = static_cast<int32_t>(block->GetLength());
    outdegree = boost::out_degree(v, g);
    indegree = boost::in_degree(v, g);
    spp = 1;
    isRecursive = false;
    int32_t distanceToEntry = -1;
    int32_t distanceToExit = -1; // TODO:
    int callCount = 0;
    
    auto distToEntry = entryDistances.find(v);
    if (distToEntry != entryDistances.end()) {
      distanceToEntry = static_cast<int32_t>(distToEntry->second);
    }
    
    for (size_t addr = block->GetStart(); addr < block->GetEnd(); addr++) {
      size_t i = func->GetLowLevelILForInstruction(arch, addr);
      size_t index = llil->GetIndexForInstruction(i);
      if (index == std::numeric_limits<uint64_t>::max())
        continue;
      
      BNLowLevelILInstruction il = llil->operator[](index);
      
      spp *= PRIMES[il.operation];
      
      switch (il.operation) {
        case LLIL_CALL:
        case LLIL_SYSCALL:
          ++callCount;
          break;
        case LLIL_JUMP:
          if (il.sourceOperand >= block->GetStart() && il.sourceOperand <= block->GetEnd())
            isRecursive = true;
          break;
        default:
          break;
      }
    }
    
    sqlite::statement stmt(db.prepare_statement(
      "INSERT INTO basic_blocks "
      "(function_id, address, length, spp, indegree, outdegree, is_recursive, distance_to_entry, distance_to_exit, call_count) "
      "VALUES (:function_id, :address, :length, :spp, :indegree, :outdegree, :is_recursive, :distance_to_entry, :distance_to_exit, :call_count)"
    ));
    stmt.bind(":function_id", functionID);
    stmt.bind(":address", address);
    stmt.bind(":length", length);
    stmt.bind(":spp", spp);
    stmt.bind(":indegree", indegree);
    stmt.bind(":outdegree", outdegree);
    stmt.bind(":is_recursive", isRecursive);
    stmt.bind(":distance_to_entry", distanceToEntry);
    stmt.bind(":distance_to_exit", distanceToExit);
    stmt.bind(":call_count", callCount);
    
    sqlite::result results(db.execute(stmt));
  }
}

vector<string> split(const string& s, char delim) {
  vector<string> elems;
  stringstream ss;
  ss.str(s);
  
  string item;
  while (getline(ss, item, delim)) {
    elems.push_back(item);
  }
  
  return elems;
}

extern "C"
{
  BINARYNINJAPLUGIN bool CorePluginInit()
  {
    // Register the plugin with Binary Ninja
    BN::PluginCommand::Register("Save Function Database",
                                "Create a database holding function metadata and symbols.",
                                &saveDatabase);
    return true;
  }
}
