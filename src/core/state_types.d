module core.state_types;

import io.parameters;
import io.network;

import core.knowledge;

struct ZoO_state {
	ZoO_parameters param;
	ZoO_knowledge knowledge;
	ZoO_network network;
}
