// #[derive(Debug, PartialEq)]
// struct EncodedShape {
//     ctl_bytes_len: usize,
//     complete_ctl_bytes_len: usize,
//     leftover_numbers: usize,
// }

// fn encoded_shape(count: usize) -> EncodedShape {
//     EncodedShape {
//         control_bytes_len: (count + 3) / 4,
//         complete_control_bytes_len: count / 4,
//         leftover_numbers: count % 4,
//     }
// }

// pub fn encode_quads(input: &[u32], ctl: &mut [u8], buf: &mut [u8]) -> (usize, usize) {
//     let mut bytes_written = 0;
//     let mut nums_encoded = 0;

//     for quads_encoded in 0..control_bytes.len() {
//         let num0 = input[nums_encoded];
//         let num1 = input[nums_encoded + 1];
//         let num2 = input[nums_encoded + 2];
//         let num3 = input[nums_encoded + 3];

//         let len0 = encode_num_scalar(num0, &mut encoded_nums[bytes_written..]);
//         let len1 = encode_num_scalar(num1, &mut encoded_nums[bytes_written + len0..]);
//         let len2 = encode_num_scalar(num2, &mut encoded_nums[bytes_written + len0 + len1..]);
//         let len3 = encode_num_scalar(
//             num3,
//             &mut encoded_nums[bytes_written + len0 + len1 + len2..],
//         );

//         // this is a few percent faster in my testing than using control_bytes.iter_mut()
//         control_bytes[quads_encoded] =
//             ((len0 - 1) | (len1 - 1) << 2 | (len2 - 1) << 4 | (len3 - 1) << 6) as u8;

//         bytes_written += len0 + len1 + len2 + len3;
//         nums_encoded += 4;
//     }

//     (nums_encoded, bytes_written)
// }
