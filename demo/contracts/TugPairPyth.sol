// SPDX-License-Identifier: MIT
pragma solidity 0.8.13;

/// @title IPythEvents contains the events that Pyth contract emits.
/// @dev This interface can be used for listening to the updates for off-chain and testing purposes.
interface IPythEvents {
    /// @dev Emitted when the price feed with `id` has received a fresh update.
    /// @param id The Pyth Price Feed ID.
    /// @param publishTime Publish time of the given price update.
    /// @param price Price of the given price update.
    /// @param conf Confidence interval of the given price update.
    event PriceFeedUpdate(
        bytes32 indexed id,
        uint64 publishTime,
        int64 price,
        uint64 conf
    );

    /// @dev Emitted when a batch price update is processed successfully.
    /// @param chainId ID of the source chain that the batch price update comes from.
    /// @param sequenceNumber Sequence number of the batch price update.
    event BatchPriceFeedUpdate(uint16 chainId, uint64 sequenceNumber);
}

// File: @pythnetwork/pyth-sdk-solidity/PythStructs.sol


pragma solidity ^0.8.0;

contract PythStructs {
    // A price with a degree of uncertainty, represented as a price +- a confidence interval.
    //
    // The confidence interval roughly corresponds to the standard error of a normal distribution.
    // Both the price and confidence are stored in a fixed-point numeric representation,
    // `x * (10^expo)`, where `expo` is the exponent.
    //
    // Please refer to the documentation at https://docs.pyth.network/consumers/best-practices for how
    // to how this price safely.
    struct Price {
        // Price
        int64 price;
        // Confidence interval around the price
        uint64 conf;
        // Price exponent
        int32 expo;
        // Unix timestamp describing when the price was published
        uint publishTime;
    }

    // PriceFeed represents a current aggregate price from pyth publisher feeds.
    struct PriceFeed {
        // The price ID.
        bytes32 id;
        // Latest available price
        Price price;
        // Latest available exponentially-weighted moving average price
        Price emaPrice;
    }
}

// File: @pythnetwork/pyth-sdk-solidity/IPyth.sol


pragma solidity ^0.8.0;



/// @title Consume prices from the Pyth Network (https://pyth.network/).
/// @dev Please refer to the guidance at https://docs.pyth.network/consumers/best-practices for how to consume prices safely.
/// @author Pyth Data Association
interface IPyth is IPythEvents {
    /// @notice Returns the period (in seconds) that a price feed is considered valid since its publish time
    function getValidTimePeriod() external view returns (uint validTimePeriod);

    /// @notice Returns the price and confidence interval.
    /// @dev Reverts if the price has not been updated within the last `getValidTimePeriod()` seconds.
    /// @param id The Pyth Price Feed ID of which to fetch the price and confidence interval.
    /// @return price - please read the documentation of PythStructs.Price to understand how to use this safely.
    function getPrice(
        bytes32 id
    ) external view returns (PythStructs.Price memory price);

    /// @notice Returns the exponentially-weighted moving average price and confidence interval.
    /// @dev Reverts if the EMA price is not available.
    /// @param id The Pyth Price Feed ID of which to fetch the EMA price and confidence interval.
    /// @return price - please read the documentation of PythStructs.Price to understand how to use this safely.
    function getEmaPrice(
        bytes32 id
    ) external view returns (PythStructs.Price memory price);

    /// @notice Returns the price of a price feed without any sanity checks.
    /// @dev This function returns the most recent price update in this contract without any recency checks.
    /// This function is unsafe as the returned price update may be arbitrarily far in the past.
    ///
    /// Users of this function should check the `publishTime` in the price to ensure that the returned price is
    /// sufficiently recent for their application. If you are considering using this function, it may be
    /// safer / easier to use either `getPrice` or `getPriceNoOlderThan`.
    /// @return price - please read the documentation of PythStructs.Price to understand how to use this safely.
    function getPriceUnsafe(
        bytes32 id
    ) external view returns (PythStructs.Price memory price);

    /// @notice Returns the price that is no older than `age` seconds of the current time.
    /// @dev This function is a sanity-checked version of `getPriceUnsafe` which is useful in
    /// applications that require a sufficiently-recent price. Reverts if the price wasn't updated sufficiently
    /// recently.
    /// @return price - please read the documentation of PythStructs.Price to understand how to use this safely.
    function getPriceNoOlderThan(
        bytes32 id,
        uint age
    ) external view returns (PythStructs.Price memory price);

    /// @notice Returns the exponentially-weighted moving average price of a price feed without any sanity checks.
    /// @dev This function returns the same price as `getEmaPrice` in the case where the price is available.
    /// However, if the price is not recent this function returns the latest available price.
    ///
    /// The returned price can be from arbitrarily far in the past; this function makes no guarantees that
    /// the returned price is recent or useful for any particular application.
    ///
    /// Users of this function should check the `publishTime` in the price to ensure that the returned price is
    /// sufficiently recent for their application. If you are considering using this function, it may be
    /// safer / easier to use either `getEmaPrice` or `getEmaPriceNoOlderThan`.
    /// @return price - please read the documentation of PythStructs.Price to understand how to use this safely.
    function getEmaPriceUnsafe(
        bytes32 id
    ) external view returns (PythStructs.Price memory price);

    /// @notice Returns the exponentially-weighted moving average price that is no older than `age` seconds
    /// of the current time.
    /// @dev This function is a sanity-checked version of `getEmaPriceUnsafe` which is useful in
    /// applications that require a sufficiently-recent price. Reverts if the price wasn't updated sufficiently
    /// recently.
    /// @return price - please read the documentation of PythStructs.Price to understand how to use this safely.
    function getEmaPriceNoOlderThan(
        bytes32 id,
        uint age
    ) external view returns (PythStructs.Price memory price);

    /// @notice Update price feeds with given update messages.
    /// This method requires the caller to pay a fee in wei; the required fee can be computed by calling
    /// `getUpdateFee` with the length of the `updateData` array.
    /// Prices will be updated if they are more recent than the current stored prices.
    /// The call will succeed even if the update is not the most recent.
    /// @dev Reverts if the transferred fee is not sufficient or the updateData is invalid.
    /// @param updateData Array of price update data.
    function updatePriceFeeds(bytes[] calldata updateData) external payable;

    /// @notice Wrapper around updatePriceFeeds that rejects fast if a price update is not necessary. A price update is
    /// necessary if the current on-chain publishTime is older than the given publishTime. It relies solely on the
    /// given `publishTimes` for the price feeds and does not read the actual price update publish time within `updateData`.
    ///
    /// This method requires the caller to pay a fee in wei; the required fee can be computed by calling
    /// `getUpdateFee` with the length of the `updateData` array.
    ///
    /// `priceIds` and `publishTimes` are two arrays with the same size that correspond to senders known publishTime
    /// of each priceId when calling this method. If all of price feeds within `priceIds` have updated and have
    /// a newer or equal publish time than the given publish time, it will reject the transaction to save gas.
    /// Otherwise, it calls updatePriceFeeds method to update the prices.
    ///
    /// @dev Reverts if update is not needed or the transferred fee is not sufficient or the updateData is invalid.
    /// @param updateData Array of price update data.
    /// @param priceIds Array of price ids.
    /// @param publishTimes Array of publishTimes. `publishTimes[i]` corresponds to known `publishTime` of `priceIds[i]`
    function updatePriceFeedsIfNecessary(
        bytes[] calldata updateData,
        bytes32[] calldata priceIds,
        uint64[] calldata publishTimes
    ) external payable;

    /// @notice Returns the required fee to update an array of price updates.
    /// @param updateData Array of price update data.
    /// @return feeAmount The required fee in Wei.
    function getUpdateFee(
        bytes[] calldata updateData
    ) external view returns (uint feeAmount);

    /// @notice Parse `updateData` and return price feeds of the given `priceIds` if they are all published
    /// within `minPublishTime` and `maxPublishTime`.
    ///
    /// You can use this method if you want to use a Pyth price at a fixed time and not the most recent price;
    /// otherwise, please consider using `updatePriceFeeds`. This method does not store the price updates on-chain.
    ///
    /// This method requires the caller to pay a fee in wei; the required fee can be computed by calling
    /// `getUpdateFee` with the length of the `updateData` array.
    ///
    ///
    /// @dev Reverts if the transferred fee is not sufficient or the updateData is invalid or there is
    /// no update for any of the given `priceIds` within the given time range.
    /// @param updateData Array of price update data.
    /// @param priceIds Array of price ids.
    /// @param minPublishTime minimum acceptable publishTime for the given `priceIds`.
    /// @param maxPublishTime maximum acceptable publishTime for the given `priceIds`.
    /// @return priceFeeds Array of the price feeds corresponding to the given `priceIds` (with the same order).
    function parsePriceFeedUpdates(
        bytes[] calldata updateData,
        bytes32[] calldata priceIds,
        uint64 minPublishTime,
        uint64 maxPublishTime
    ) external payable returns (PythStructs.PriceFeed[] memory priceFeeds);
}

// File: TokenRegistryPyth.sol

/// @notice Arithmetic library with operations for fixed-point numbers.
/// @author Solmate (https://github.com/Rari-Capital/solmate/blob/main/src/utils/FixedPointMathLib.sol)
/// @author Inspired by USM (https://github.com/usmfum/USM/blob/master/contracts/WadMath.sol)
library FixedPointMathLib {
    /*//////////////////////////////////////////////////////////////
                    SIMPLIFIED FIXED POINT OPERATIONS
    //////////////////////////////////////////////////////////////*/

    uint256 internal constant WAD = 1e18; // The scalar of ETH and most ERC20s.

    function mulWadDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, y, WAD); // Equivalent to (x * y) / WAD rounded down.
    }

    function mulWadUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, y, WAD); // Equivalent to (x * y) / WAD rounded up.
    }

    function divWadDown(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivDown(x, WAD, y); // Equivalent to (x * WAD) / y rounded down.
    }

    function divWadUp(uint256 x, uint256 y) internal pure returns (uint256) {
        return mulDivUp(x, WAD, y); // Equivalent to (x * WAD) / y rounded up.
    }

    /*//////////////////////////////////////////////////////////////
                    LOW LEVEL FIXED POINT OPERATIONS
    //////////////////////////////////////////////////////////////*/

    function mulDivDown(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require(denominator != 0 && (x == 0 || (x * y) / x == y))
            if iszero(and(iszero(iszero(denominator)), or(iszero(x), eq(div(z, x), y)))) {
                revert(0, 0)
            }

            // Divide z by the denominator.
            z := div(z, denominator)
        }
    }

    function mulDivUp(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 z) {
        assembly {
            // Store x * y in z for now.
            z := mul(x, y)

            // Equivalent to require(denominator != 0 && (x == 0 || (x * y) / x == y))
            if iszero(and(iszero(iszero(denominator)), or(iszero(x), eq(div(z, x), y)))) {
                revert(0, 0)
            }

            // First, divide z - 1 by the denominator and add 1.
            // We allow z - 1 to underflow if z is 0, because we multiply the
            // end result by 0 if z is zero, ensuring we return 0 if z is zero.
            z := mul(iszero(iszero(z)), add(div(sub(z, 1), denominator), 1))
        }
    }

    function rpow(
        uint256 x,
        uint256 n,
        uint256 scalar
    ) internal pure returns (uint256 z) {
        assembly {
            switch x
            case 0 {
                switch n
                case 0 {
                    // 0 ** 0 = 1
                    z := scalar
                }
                default {
                    // 0 ** n = 0
                    z := 0
                }
            }
            default {
                switch mod(n, 2)
                case 0 {
                    // If n is even, store scalar in z for now.
                    z := scalar
                }
                default {
                    // If n is odd, store x in z for now.
                    z := x
                }

                // Shifting right by 1 is like dividing by 2.
                let half := shr(1, scalar)

                for {
                    // Shift n right by 1 before looping to halve it.
                    n := shr(1, n)
                } n {
                    // Shift n right by 1 each iteration to halve it.
                    n := shr(1, n)
                } {
                    // Revert immediately if x ** 2 would overflow.
                    // Equivalent to iszero(eq(div(xx, x), x)) here.
                    if shr(128, x) {
                        revert(0, 0)
                    }

                    // Store x squared.
                    let xx := mul(x, x)

                    // Round to the nearest number.
                    let xxRound := add(xx, half)

                    // Revert if xx + half overflowed.
                    if lt(xxRound, xx) {
                        revert(0, 0)
                    }

                    // Set x to scaled xxRound.
                    x := div(xxRound, scalar)

                    // If n is even:
                    if mod(n, 2) {
                        // Compute z * x.
                        let zx := mul(z, x)

                        // If z * x overflowed:
                        if iszero(eq(div(zx, x), z)) {
                            // Revert if x is non-zero.
                            if iszero(iszero(x)) {
                                revert(0, 0)
                            }
                        }

                        // Round to the nearest number.
                        let zxRound := add(zx, half)

                        // Revert if zx + half overflowed.
                        if lt(zxRound, zx) {
                            revert(0, 0)
                        }

                        // Return properly scaled zxRound.
                        z := div(zxRound, scalar)
                    }
                }
            }
        }
    }

    /*//////////////////////////////////////////////////////////////
                        GENERAL NUMBER UTILITIES
    //////////////////////////////////////////////////////////////*/

    function sqrt(uint256 x) internal pure returns (uint256 z) {
        assembly {
            // Start off with z at 1.
            z := 1

            // Used below to help find a nearby power of 2.
            let y := x

            // Find the lowest power of 2 that is at least sqrt(x).
            if iszero(lt(y, 0x100000000000000000000000000000000)) {
                y := shr(128, y) // Like dividing by 2 ** 128.
                z := shl(64, z) // Like multiplying by 2 ** 64.
            }
            if iszero(lt(y, 0x10000000000000000)) {
                y := shr(64, y) // Like dividing by 2 ** 64.
                z := shl(32, z) // Like multiplying by 2 ** 32.
            }
            if iszero(lt(y, 0x100000000)) {
                y := shr(32, y) // Like dividing by 2 ** 32.
                z := shl(16, z) // Like multiplying by 2 ** 16.
            }
            if iszero(lt(y, 0x10000)) {
                y := shr(16, y) // Like dividing by 2 ** 16.
                z := shl(8, z) // Like multiplying by 2 ** 8.
            }
            if iszero(lt(y, 0x100)) {
                y := shr(8, y) // Like dividing by 2 ** 8.
                z := shl(4, z) // Like multiplying by 2 ** 4.
            }
            if iszero(lt(y, 0x10)) {
                y := shr(4, y) // Like dividing by 2 ** 4.
                z := shl(2, z) // Like multiplying by 2 ** 2.
            }
            if iszero(lt(y, 0x8)) {
                // Equivalent to 2 ** z.
                z := shl(1, z)
            }

            // Shifting right by 1 is like dividing by 2.
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))
            z := shr(1, add(z, div(x, z)))

            // Compute a rounded down version of z.
            let zRoundDown := div(x, z)

            // If zRoundDown is smaller, use it.
            if lt(zRoundDown, z) {
                z := zRoundDown
            }
        }
    }
}


// OpenZeppelin Contracts v4.4.1 (access/Ownable.sol)




// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)



/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}


// OpenZeppelin Contracts v4.4.1 (security/Pausable.sol)





/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        require(!paused(), "Pausable: paused");
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        require(paused(), "Pausable: not paused");
        _;
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}


// OpenZeppelin Contracts (last updated v4.5.0) (token/ERC20/IERC20.sol)



/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}




interface TugPairInterface {
    /// @notice Emitted at start of epoch
    event EpochStarted(uint256 indexed epoch);
    /// @notice Emitted at end of epoch
    event EpochEnded(uint256 indexed epoch);
    /// @notice User deposited DAI
    event Deposit(
        uint256 indexed epoch,
        address indexed user,
        uint8 indexed side,
        uint256 usdAmount,
        uint256 sharesIssued
    );
    /// @notice User collect DAI winnings
    event Collection(
        uint256 indexed epoch,
        address indexed user,
        uint256 usdCollected
    );

    /// @notice Returns the address of the deposit token used.
    function getDepositToken() external returns (address depositToken);

    /// @notice Returns the latest epoch
    function getLatestEpoch() external returns (uint256 newEpoch);

    /// @notice Deposits DAI into the current active epoch. Requires token approval.
    /// @param _amount amount of DAI to be deposit
    function deposit(uint256 _amount, uint8 _side, bytes[] calldata priceUpdateData) external payable;

    /// @notice Collect DAI winnings for given epochs
    /// @param _epochs Epochs for which we want to collect winnings for
    function collectWinnings(uint256[] calldata _epochs, bytes[] calldata priceUpdateData) external payable;

    /// @notice Collect DAI winnings for given epochs
    /// @param _epochs Epochs for which we want to collect winnings for
    function collectWinningsPerEpoch(uint256 _epochs, bytes[] calldata priceUpdateData) external payable;

    function collectWinningsPerEpochWithoutUpdateEpoch(uint256 _epochs) external payable;

    /// @notice Returns amount of DAI winnings available for user for given epoch.
    /// @return amountOfDaiWinnings amount of DAI available for collection for epoch. 0 if invalid epoch.
    function getWinnings(uint256 _epoch, address _user)
        external
        view
        returns (uint256 amountOfDaiWinnings);
}




interface TugStorageInterface {
    // Deploy status
    function getDeployedStatus() external view returns (bool);

    // Guardians
    function getGuardian() external view returns (address);

    function setGuardian(address _newAddress) external;

    function confirmGuardian() external;

    // Getters
    function getAddress(bytes32 _key) external view returns (address);

    function getUint(bytes32 _key) external view returns (uint256);

    function getString(bytes32 _key) external view returns (string memory);

    function getBytes(bytes32 _key) external view returns (bytes memory);

    function getBool(bytes32 _key) external view returns (bool);

    function getInt(bytes32 _key) external view returns (int256);

    function getBytes32(bytes32 _key) external view returns (bytes32);

    // Setters
    function setAddress(bytes32 _key, address _value) external;

    function setUint(bytes32 _key, uint256 _value) external;

    function setString(bytes32 _key, string calldata _value) external;

    function setBytes(bytes32 _key, bytes calldata _value) external;

    function setBool(bytes32 _key, bool _value) external;

    function setInt(bytes32 _key, int256 _value) external;

    function setBytes32(bytes32 _key, bytes32 _value) external;

    // Deleters
    function deleteAddress(bytes32 _key) external;

    function deleteUint(bytes32 _key) external;

    function deleteString(bytes32 _key) external;

    function deleteBytes(bytes32 _key) external;

    function deleteBool(bytes32 _key) external;

    function deleteInt(bytes32 _key) external;

    function deleteBytes32(bytes32 _key) external;

    // Arithmetic
    function addUint(bytes32 _key, uint256 _amount) external;

    function subUint(bytes32 _key, uint256 _amount) external;

    // Known frequent queries to reduce calldata gas
    function getPricingEngineAddress() external view returns (address);

    function getTreasuryAddress() external view returns (address);

    function getTokenRegistryAddress() external view returns (address);
}




interface PricingEngineInterface {
    /// @notice Computes the USD price per tug share, given to a predetermined decimal
    /// @param _startTime The start time of the current tug period
    /// @param _endTime The time the current tug will end
    /// @param _purchaseTime The timestamp for the given investment
    /// @param _token0StartPrice The price of token0 at the start of tug
    /// @param _token1StartPrice The price of token1 at the start of tug
    /// @param _token0Index Index of the first token
    /// @param _token1Index Index of the second token
    /// @param _buyDirection 0 if buying token0, 1 if buying token1
    /// @return price USD price per share
    function getUsdPerShare(
        uint256 _startTime,
        uint256 _endTime,
        uint256 _purchaseTime,
        uint256 _token0StartPrice,
        uint256 _token1StartPrice,
        uint8 _token0Index,
        uint8 _token1Index,
        uint8 _buyDirection,
        uint256 token0Price,
        uint256 token1Price
    ) external pure returns (uint256 price);

    /// @notice Returns the corresponding decimals for the `getUsdPerShare()` call.
    /// @dev Seperated to save gas costs as this is not needed as a return value in the usual calculation.
    function getSharePriceDecimal() external pure returns (uint8 decimals);
}




interface TokenRegistryInterface {
    /// @notice Emitted when a new token is registered with the protocol
    event TokenRegistered(string symbol, uint8 index);

    /// @notice Obtain the priceId of a given index
    function getPriceID(uint256 _index) external view returns (bytes32);

    /// @notice Obtain the symbol of a given index
    function getSymbol(uint8 _index) external returns (string calldata symbol);

    /// @notice Given a string, return the associated token index
    function getTokenIndex(string calldata _symbol)
        external
        returns (uint8 index);

    /// @notice Registers a new token for use in Tug
    /// @param _symbol Associated String for human readability
    /// @param _chainlinkOracle Chainlink oracle address to be used to get price
    /// @return index of the new token.
    // function registerToken(string calldata _symbol, address _chainlinkOracle) external returns (uint index);
}


contract TugPair is TugPairInterface, Ownable, Pausable {
    using FixedPointMathLib for uint256;

    struct EpochData {
        uint256 token0InitialPrice; // initial price of token set during epoch initialization
        uint256 token1InitialPrice; // initial price of token set during epoch initialization
        mapping(address => uint256) token0ShareBalance;
        uint256 token0SharesIssued;
        mapping(address => uint256) token1ShareBalance;
        uint256 token1SharesIssued;
        uint256 totalPot; // Total amount of DAI deposited by users for this epoch
        mapping(address => bool) hasAlreadyCollectedWinnnings; // mapping of whether users have already collected winnings
        int8 winningSide; // -1 if none has won yet. 0 for token0, 1 for token1
    }

    struct Tug {
        uint256 epochAmountA;
        uint256 epochAmountB;
        uint256 userLatestEpoch; 
    }

    error InvalidTokenIndex(uint8 invalidTokenIndex);
    error InvalidTokenPrice(uint8 tokenIndexWithInvalidPrice);
    error EpochDurationIsZero();
    error DepositIsZero();
    error InvalidDepositSide(uint8 invalidSide);
    error CannotDepositToEpochZero();
    error DepositTooLow(uint256 amount);
    error EpochNotConcluded(uint256 epoch);
    error EpochPreviouslyConcluded(uint256 epoch);
    error EpochOutOfSync(uint256 currentEpoch);
    error InvalidSharePrice();
    error EpochWinningsAlreadyClaimed(uint256 epoch, address user);
    error InvalidTreasuryAddress();
    error TokenTransferFailed();

    TugStorageInterface public immutable tugStorage;
    PricingEngineInterface public immutable pricingEngine;
    TokenRegistryInterface public immutable tokenRegistry;
    IERC20 public immutable depositToken;
    uint8 public immutable token0Index;
    uint8 public immutable token1Index;
    uint256 public immutable startTime;
    uint256 public immutable epochDuration;
    uint256 public currentEpoch;
    mapping(uint256 => EpochData) public epochData;
    mapping(address => Tug) public currentTug;
    uint256 public accumulatedFees;
    uint256 private latestToken0Price;
    uint256 private latestToken1Price;

    uint256 public constant FEE = 10; // out of 10,000 - 0.10%
    uint256 public constant WIN_SIDE_MUL = 7900; // out of 10,000 - 79%
    uint256 public constant WIN_FEE = 100; // out of 10,000 - 1%
    uint256 public constant LOSE_SIDE_MUL = 2000; // out of 10,000 - 20%

    IPyth pyth = IPyth(0xC38B1dd611889Abc95d4E0a472A667c3671c08DE);

    constructor(
        address _tugStorageAddress,
        address _depositToken,
        uint8 _token0Index,
        uint8 _token1Index,
        uint256 _startTime,
        uint256 _epochDuration
    ) {
        if (_token0Index == 0) revert InvalidTokenIndex(_token0Index);
        if (_token1Index == 0) revert InvalidTokenIndex(_token1Index);
        if (_epochDuration == 0) revert EpochDurationIsZero(); // prevent dividing by 0 when calculating price
        tugStorage = TugStorageInterface(_tugStorageAddress);

        // Fixed at initialization to ensure that admins have decreased influence over economics
        pricingEngine = PricingEngineInterface(
            tugStorage.getPricingEngineAddress()
        );
        tokenRegistry = TokenRegistryInterface(
            tugStorage.getTokenRegistryAddress()
        );

        depositToken = IERC20(_depositToken);
        token0Index = _token0Index;
        token1Index = _token1Index;
        startTime = _startTime;
        epochDuration = _epochDuration;
    }

    // ------------ View Functions ------------ //
    /// @inheritdoc TugPairInterface
    function getDepositToken()
        external
        view
        override
        returns (address depositTokenToReturn)
    {
        depositTokenToReturn = address(depositToken);
    }

    /// @inheritdoc TugPairInterface
    function getLatestEpoch()
        external
        view
        override
        returns (uint256 latestEpoch)
    {
        latestEpoch = currentEpoch;
    }

    /// @notice Returns true if the given epoch has already ended.
    function epochEnded(uint256 epochToCheck) private view returns (bool) {
        uint256 epochEndTime = startTime + epochToCheck * epochDuration;
        return block.timestamp >= epochEndTime;
    }

    /// @notice Returns the amount of shares to distribute in the current block for given amount and side.
    /// @param _amount # of deposit tokens to deposit (DAI)
    /// @param _side Side to deposit DAI on. 0 for token0, 1 for token 1
    /// @return qtyOfShares to be issued
    function getQtyOfSharesToIssue(uint256 _amount, uint8 _side)
        public
        view
        returns (uint256 qtyOfShares)
    {
        uint256 sharePrice = pricingEngine.getUsdPerShare(
            startTime + (currentEpoch - 1) * epochDuration, // start time of epoch
            startTime + currentEpoch * epochDuration, // end time of epoch
            block.timestamp,
            epochData[currentEpoch].token0InitialPrice,
            epochData[currentEpoch].token1InitialPrice,
            token0Index,
            token1Index,
            _side,
            latestToken0Price,
            latestToken1Price
        );
        uint8 shareDecimal = pricingEngine.getSharePriceDecimal();

        // Rounded down to avoid exploitation by using very small deposits to get 1 share. Unlikely to be profitable due to chain fees but possible.
        qtyOfShares = _amount.mulDivDown(10**shareDecimal, sharePrice);
    }

    /// @notice Returns the share balance for a given epoch
    function getSharesBalance(uint256 epochToCheck, address user)
        external
        view
        returns (uint256 token0Shares, uint256 token1Shares)
    {
        token0Shares = epochData[epochToCheck].token0ShareBalance[user];
        token1Shares = epochData[epochToCheck].token1ShareBalance[user];
    }

    /// @notice Returns the shares issued so far for a given epoch
    function getSharesIssued(uint256 epochToCheck)
        external
        view
        returns (uint256 token0SharesIssued, uint256 token1SharesIssued)
    {
        token0SharesIssued = epochData[epochToCheck].token0SharesIssued;
        token1SharesIssued = epochData[epochToCheck].token1SharesIssued;
    }

    /// @inheritdoc TugPairInterface
    /// @dev Winnings = (# shares / total shares issued) * (totalPot * side multiplier). Rounded down to prevent paying out more than what we have.
    function getWinnings(uint256 _epoch, address _user)
        public
        view
        override
        returns (uint256 amountOfDaiWinnings)
    {
        EpochData storage thisEpochData = epochData[_epoch];
        int8 winningSide = thisEpochData.winningSide;
        if (_epoch > currentEpoch || winningSide == -1)
            revert EpochNotConcluded(_epoch); // if _epoch is higher than current, winningSide is still 0.

        uint256 token0SharesIssued = thisEpochData.token0SharesIssued;
        if (token0SharesIssued > 0) {
            uint256 token0SideMultipler = winningSide == 0
                ? WIN_SIDE_MUL
                : LOSE_SIDE_MUL;
            amountOfDaiWinnings += thisEpochData
                .token0ShareBalance[_user]
                .mulDivDown(
                    thisEpochData.totalPot.mulDivDown(
                        token0SideMultipler,
                        10000
                    ),
                    thisEpochData.token0SharesIssued
                );
        }

        uint256 token1SharesIssued = thisEpochData.token1SharesIssued;
        if (token1SharesIssued > 0) {
            uint256 token1SideMultipler = winningSide == 1
                ? WIN_SIDE_MUL
                : LOSE_SIDE_MUL;
            amountOfDaiWinnings += thisEpochData
                .token1ShareBalance[_user]
                .mulDivDown(
                    thisEpochData.totalPot.mulDivDown(
                        token1SideMultipler,
                        10000
                    ),
                    thisEpochData.token1SharesIssued
                );
        }
    }

    // ------------ Mutative Functions ------------ //
    /// @notice Closes the epoch and sets the winner according to current ratio.
    /// @param _epoch Epoch to close.
    /// @dev Only call after checking that the end-time for this epoch has already passed.
    function concludeEpoch(uint256 _epoch, uint256 currentToken0Price, uint256 currentToken1Price) private {
        if (epochData[_epoch].winningSide == -1) {
            // Only update once
            uint256 oldToken0Price = epochData[_epoch].token0InitialPrice;
            uint256 oldToken1Price = epochData[_epoch].token1InitialPrice;
            uint256 oldRatio = oldToken0Price.mulDivUp(10000, oldToken1Price);

            uint256 currentRatio = currentToken0Price.mulDivUp(10000, currentToken1Price);

            if (currentRatio > oldRatio) {
                epochData[_epoch].winningSide = 0;
            } else {
                epochData[_epoch].winningSide = 1;
            }

            accumulatedFees += epochData[_epoch].totalPot.mulDivDown(
                WIN_FEE,
                10000
            );

            emit EpochEnded(_epoch);
        }
    }

    function getPrice(
        uint8 _index1,
        uint8 _index2,
        bytes[] calldata priceUpdateData
    ) public payable returns (uint256 price1, uint256 price2, uint8 decimal1, uint8 decimal2) {
        // Update the prices to the latest available values and pay the required fee for it. The `priceUpdateData` data
        // should be retrieved from our off-chain Price Service API using the `pyth-evm-js` package.
        // See section "How Pyth Works on EVM Chains" below for more information.
        uint fee = pyth.getUpdateFee(priceUpdateData);
        pyth.updatePriceFeeds{ value: fee }(priceUpdateData);

        bytes32 priceID1 = tokenRegistry.getPriceID(_index1);
        bytes32 priceID2 = tokenRegistry.getPriceID(_index2);

        // Read the current value of priceID, aborting the transaction if the price has not been updated recently.
        // Every chain has a default recency threshold which can be retrieved by calling the getValidTimePeriod() function on the contract.
        // Please see IPyth.sol for variants of this function that support configurable recency thresholds and other useful features.
        price1 = convertToUint(pyth.getPrice(priceID1),18);
        price2 = convertToUint(pyth.getPrice(priceID2),18);

        decimal1 = 18;
        decimal2 = 18;
    }

    function convertToUint(
        PythStructs.Price memory price,
        uint8 targetDecimals
    ) private pure returns (uint256) {
        if (price.price < 0 || price.expo > 0 || price.expo < -255) {
            revert();
        }

        uint8 priceDecimals = uint8(uint32(-1 * price.expo));

        if (targetDecimals - priceDecimals >= 0) {
            return
                uint(uint64(price.price)) *
                10 ** uint32(targetDecimals - priceDecimals);
        } else {
            return
                uint(uint64(price.price)) /
                10 ** uint32(priceDecimals - targetDecimals);
        }
    }


    /// @notice Update epoch to latest. Conclude any old epochs.
    function updateEpoch(bytes[] calldata priceUpdateData) public payable {
        (latestToken0Price, latestToken1Price,,) = getPrice(token0Index, token1Index, priceUpdateData);

        while (epochEnded(currentEpoch)) {
            // Keeps progressing epoch until it's up to date.
            uint256 oldCurrentEpoch = currentEpoch;
            if (oldCurrentEpoch != 0) {
                // epoch 0 doesn't exist and doesn't need to be concluded
                concludeEpoch(oldCurrentEpoch, latestToken0Price, latestToken1Price);
            }
            uint256 newEpoch = ++oldCurrentEpoch;
            currentEpoch = newEpoch;

            uint256 token0InitialPrice = latestToken0Price;
            if (token0InitialPrice == 0) revert InvalidTokenPrice(token0Index);
            epochData[newEpoch].token0InitialPrice = token0InitialPrice;

            uint256 token1InitialPrice = latestToken1Price;
            if (token1InitialPrice == 0) revert InvalidTokenPrice(token1Index);
            epochData[newEpoch].token1InitialPrice = token1InitialPrice;

            epochData[newEpoch].winningSide = -1; // -1 indicates that neither side has won yet.
            emit EpochStarted(newEpoch);
        }
    }

    function getUserCurrentEpoch(address user)
        external
        view
        returns (uint256 latestEpoch, uint256 totalDepositA, uint256 totalDepositB)
    {
        latestEpoch = currentTug[user].userLatestEpoch;
        totalDepositA = currentTug[user].epochAmountA;
        totalDepositB = currentTug[user].epochAmountB;
    }

    /// @inheritdoc TugPairInterface
    function deposit(uint256 _amount, uint8 _side, bytes[] calldata priceUpdateData)
        external
        payable
        override
        whenNotPaused
    {
        // Checks
        if (_amount == 0) revert DepositIsZero();
        if (_side > 1) revert InvalidDepositSide(_side); // _side can only be 0 or 1
        updateEpoch(priceUpdateData);
        if (currentEpoch == 0) revert CannotDepositToEpochZero();
        if (epochEnded(currentEpoch)) revert EpochOutOfSync(currentEpoch); // Do NOT proceed with desposit if the current epoch has already ended.
        if(currentTug[msg.sender].userLatestEpoch != 0 && currentEpoch >  currentTug[msg.sender].userLatestEpoch) {
            collectWinningsPerEpochWithoutUpdateEpoch(currentTug[msg.sender].userLatestEpoch);
        }

        currentTug[msg.sender].userLatestEpoch = currentEpoch;
        // Effects
        uint256 feeToCollect = _amount.mulDivDown(FEE, 10000);
        accumulatedFees += feeToCollect;
        uint256 depositAmountAfterFees = _amount - feeToCollect;
        epochData[currentEpoch].totalPot += depositAmountAfterFees;
        if(_side == 0) {
            currentTug[msg.sender].epochAmountA += depositAmountAfterFees;
        } else {
            currentTug[msg.sender].epochAmountB += depositAmountAfterFees;

        }
    
        uint256 qtySharesToIssue = getQtyOfSharesToIssue(
            depositAmountAfterFees,
            _side
        );

        if (qtySharesToIssue == 0) revert DepositTooLow(_amount);
        if (_side == 0) {
            epochData[currentEpoch].token0ShareBalance[
                _msgSender()
            ] += qtySharesToIssue;
            epochData[currentEpoch].token0SharesIssued += qtySharesToIssue;
        } else {
            epochData[currentEpoch].token1ShareBalance[
                _msgSender()
            ] += qtySharesToIssue;
            epochData[currentEpoch].token1SharesIssued += qtySharesToIssue;
        }

        emit Deposit(
            currentEpoch,
            _msgSender(),
            _side,
            _amount,
            qtySharesToIssue
        );

        // Interactions
        bool success = depositToken.transferFrom(
            _msgSender(),
            address(this),
            _amount
        );
        if (!success) revert TokenTransferFailed();
    }

    /// @inheritdoc TugPairInterface
    function collectWinnings(uint256[] calldata _epochs, bytes[] calldata priceUpdateData) public payable override {
        updateEpoch(priceUpdateData);
        currentTug[msg.sender].userLatestEpoch = 0;
        currentTug[msg.sender].epochAmountA = 0;
        currentTug[msg.sender].epochAmountB = 0;
        uint256 amountToSendUser = 0;
        for (uint256 i = 0; i < _epochs.length; ++i) {
            // Checks
            if (
                !epochData[_epochs[i]].hasAlreadyCollectedWinnnings[
                    _msgSender()
                ]
            ) {
                uint256 epochWinnings = getWinnings(_epochs[i], _msgSender());
                // Effects
                epochData[_epochs[i]].hasAlreadyCollectedWinnnings[
                    _msgSender()
                ] = true;
                amountToSendUser += epochWinnings;
                emit Collection(_epochs[i], _msgSender(), epochWinnings);
            } else {
                revert EpochWinningsAlreadyClaimed(_epochs[i], _msgSender());
            }
        }

        // Interactions
        if (amountToSendUser > 0) {
            bool success = depositToken.transfer(
                _msgSender(),
                amountToSendUser
            );
            if (!success) revert TokenTransferFailed();
        }
    }

    /// @inheritdoc TugPairInterface
    function collectWinningsPerEpoch(uint256 _epochs, bytes[] calldata priceUpdateData) public payable override {
        updateEpoch(priceUpdateData);
        uint256 amountToSendUser = 0;
            // Checks
            if (
                !epochData[_epochs].hasAlreadyCollectedWinnnings[
                    _msgSender()
                ]
            ) {
                uint256 epochWinnings = getWinnings(_epochs, _msgSender());
                // Effects
                epochData[_epochs].hasAlreadyCollectedWinnnings[
                    _msgSender()
                ] = true;
                amountToSendUser += epochWinnings;
                emit Collection(_epochs, _msgSender(), epochWinnings);
            } else {
                revert EpochWinningsAlreadyClaimed(_epochs, _msgSender());
            }

            currentTug[msg.sender].epochAmountA = 0;
            currentTug[msg.sender].epochAmountB = 0;
            currentTug[msg.sender].userLatestEpoch = 0;

        // Interactions
        if (amountToSendUser > 0) {
            bool success = depositToken.transfer(
                _msgSender(),
                amountToSendUser
            );
            if (!success) revert TokenTransferFailed();
        }
    }

    function collectWinningsPerEpochWithoutUpdateEpoch(uint256 _epochs) public payable override {
        uint256 amountToSendUser = 0;
            // Checks
            if (
                !epochData[_epochs].hasAlreadyCollectedWinnnings[
                    _msgSender()
                ]
            ) {
                uint256 epochWinnings = getWinnings(_epochs, _msgSender());
                // Effects
                epochData[_epochs].hasAlreadyCollectedWinnnings[
                    _msgSender()
                ] = true;
                amountToSendUser += epochWinnings;
                emit Collection(_epochs, _msgSender(), epochWinnings);
            } else {
                revert EpochWinningsAlreadyClaimed(_epochs, _msgSender());
            }

            currentTug[msg.sender].epochAmountA = 0;
            currentTug[msg.sender].epochAmountB = 0;
            currentTug[msg.sender].userLatestEpoch = 0;

        // Interactions
        if (amountToSendUser > 0) {
            bool success = depositToken.transfer(
                _msgSender(),
                amountToSendUser
            );
            if (!success) revert TokenTransferFailed();
        }
    }

    /// @notice Pause deposits
    function pause() external onlyOwner {
        _pause();
    }

    /// @notice Unpause deposits
    function unpause() external onlyOwner {
        _unpause();
    }

    /// @notice Send all collected fees to treasury
    function collectFees() external onlyOwner {
        address treasuryAddress = tugStorage.getTreasuryAddress();
        if (treasuryAddress == address(0)) revert InvalidTreasuryAddress();
        uint256 amtToTransfer = accumulatedFees;
        accumulatedFees = 0;
        bool success = depositToken.transfer(treasuryAddress, amtToTransfer);
        if (!success) revert TokenTransferFailed();
    }
}
