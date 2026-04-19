# WebSocket Multiplexing Protocol

Binary messages contain a complete KDP frame:

Header fields:
- magic: 4 bytes "KDP1"
- version: u16 little-endian (1)
- flags: u16 little-endian
- channel_id: u32 little-endian
- msg_type: u16 little-endian
- reserved: u16 little-endian
- seq: u64 little-endian
- ack: u64 little-endian
- payload_len: u32 little-endian
- payload: payload_len bytes

Channels:
1 editor
2 terminal
4 presence
5 control
